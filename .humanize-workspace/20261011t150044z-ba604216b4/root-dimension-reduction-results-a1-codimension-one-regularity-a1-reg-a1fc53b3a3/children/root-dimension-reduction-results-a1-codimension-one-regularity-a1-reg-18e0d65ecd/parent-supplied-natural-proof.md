# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.pushforward_rep-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.pushforward_rep-a1.integral_image_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. The final chain of equalities in step 7 of the parent proof, with f := 1_{M′}·g, separated from its use. The parent applies it with:
- m := n, d := n + 1 and its own B;
- B′ := B ∩ B_{δ₁/2}(0), G(y) := x + ιy + u(y), and the Jacobian J from area_formula;
- h(v) := −⟨Φ_ω(v), ν(v)⟩ and g(w) := ξ′(w)(ω(w)).
Notation. H^m := μHE[m]. All integrals are Bochner integrals, which are 0 for non-integrable functions. No integrability or measurability of h, J or g is used.
1. (Borel image.) ℝ^d is Polish, B′ is Borel, and G is continuous and injective on B′ ⊆ B. By Lusin–Souslin (MeasurableSet.image_of_continuousOn_injOn), M′ := G(B′) is Borel. Also M′ ⊆ G(B) (image_mono).
2. (Pull-back of the indicator.) Put f := 1_{M′}·g : ℝ^P → ℝ. Claim: J(v)·f(G(v)) = 1_{B′}(v)·J(v)·g(G(v)) for every v ∈ B.
- If v ∈ B′, then G(v) ∈ M′, so both sides equal J(v)·g(G(v)).
- Let v ∈ B ∖ B′, and suppose G(v) ∈ M′, say G(v′) = G(v) with v′ ∈ B′ ⊆ B. Injectivity of G on B gives v′ = v, so v ∈ B′, a contradiction. So f(G(v)) = 0, and both sides are 0.
3. (Replace h.) B is Borel, so H^m⌞B-a.e. v lies in B (ae_restrict_mem). By the hypothesis and step 2, h(v) = J(v)·f(G(v)) for H^m⌞B-a.e. v. Hence ∫_B h dH^m = ∫_B J·(f∘G) dH^m (integral_congr_ae).
4. (Area formula.) The hypothesis applied to this f gives ∫_B J·(f∘G) dH^m = ∫_{G(B)} f dH^m.
5. (Restrict to M′.) M′ is Borel and M′ ∩ G(B) = M′, so
 ∫_{G(B)} 1_{M′}·g dH^m = ∫ g d((H^m⌞G(B))⌞M′) (integral_indicator)
 = ∫ g d(H^m⌞(M′ ∩ G(B))) (Measure.restrict_restrict)
 = ∫_{M′} g dH^m.
6. Steps 3–5 give ∫_B h dH^m = ∫_{G(B′)} g dH^m. ∎

## Key steps

1. G(B′) is Borel by Lusin–Souslin, and G(B′) ⊆ G(B).
2. Put f := 1_{G(B′)}·g. Injectivity on B gives J·(f∘G) = 1_{B′}·J·(g∘G) on B, so h = J·(f∘G) a.e. on B.
3. The Bochner area formula gives ∫_B J·(f∘G) dH^m = ∫_{G(B)} f dH^m.
4. integral_indicator and Measure.restrict_restrict give ∫_{G(B)} 1_{G(B′)}·g dH^m = ∫_{G(B′)} g dH^m.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; python3 read of snapshot project/lake-manifest.json (mathlib, simongmt revs)`
- `sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem MeasurableSet.image_of_continuousOn_injOn|theorem measurable_fderiv_apply_const|def flipAlternating|def compContinuousLinearMap|theorem compContinuousLinearMap_apply|theorem exists_measurable_superset_of_null|theorem lintegral_indicator_one|theorem integral_indicator|theorem restrict_restrict|theorem adjoint_inner_left|theorem LinearIsometry.inner_map_map|theorem Orthonormal.linearIndependent|theorem LinearIndependent.map' <snapshot>/mathlib/Mathlib`
- `rg -n 'notation.*μHE|def MeasureTheory.Measure.euclideanHausdorffMeasure' <snapshot>/mathlib/Mathlib; rg -n 'theorem measure_eq_zero_iff_ae_notMem|theorem ae_restrict_iff|theorem ae_restrict_mem|theorem ae_restrict_of_ae|theorem integral_neg|theorem integral_congr_ae|theorem setIntegral_congr_ae' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n 'stronglyMeasurable_fun_sum|Continuous.comp_stronglyMeasurable|theorem coe_continuous|theorem ext_inner_right|theorem sum_inner|image_eq_zero_of_notMem_tsupport|theorem indicator_of_notMem' <snapshot>/mathlib/Mathlib`
- `rg -n 'def CountablyRectifiable|theorem CountablyRectifiable.mono|def HasApproximateTangentSpaceAt' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `python3 scans of dag.json (995 nodes): selected node status (decomposing, attempt 2, children []), frozen types of area_formula/normal_orientation/wedge_orientation, lean_name lookup of codim1_pfr_* (no node) and dgce_left_inverse_chart_embedded (accepted, candidate b4813988)`
- `grep -rl codim1_pfr_ <run>/nodes <run>/dag.json (only this node's unregistered v1 files); git grep -q codim1_pfr_ <each of 1828 unique ref tips> -- 'GMT/*.lean' (0 hits)`
- `git show b481398838284784de357885d0dcb4166d11434a:GMT/Ch07/Submission.lean + #print axioms; git diff b4d606db b4813988 --stat`
- `lake env lean -DautoImplicit=false /tmp/pfr2/Children.lean, /tmp/pfr2/Assembly.lean, /tmp/pfr2/AssemblyInd.lean, /tmp/pfr2/Inst.lean, /tmp/pfr2/ChildrenNoInst.lean, /tmp/pfr2/reuse/Cand.lean; reviewer /tmp/pfr2/review/Combined.lean`
- `gh issue view 5215 --repo ZhengyangZhang06/gmt-formalize --comments (no comments)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a1fc53b3a3/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a1fc53b3a3/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a1fc53b3a3/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-60926cd991/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-60926cd991/parent-child-handoff.json`
- `/tmp/pfr2/Children.lean`
- `/tmp/pfr2/Assembly.lean`
- `/tmp/pfr2/AssemblyInd.lean`
- `/tmp/pfr2/Inst.lean`
- `/tmp/pfr2/ChildrenNoInst.lean`
- `/tmp/pfr2/reuse/Cand.lean`
- `/tmp/pfr2/review/Combined.lean`

The split into one reused and three new children is sound and assembles to the exact frozen parent type.

Pins and contract:
- The snapshot manifest pins project b4d606db and Mathlib 25730c7c; the snapshot lake-manifest pins simongmt 2b366308. All three equal the workspace HEAD and its .lake packages.
- The snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library support. The snapshot provides every lemma the child proofs use:
- MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821);
- measurable_fderiv_apply_const (FDeriv/Measurable.lean:391);
- ContinuousLinearMap.flipAlternating (Normed/Module/Alternating/Basic.lean:415);
- exists_measurable_superset_of_null, lintegral_indicator_one, integral_indicator, Measure.restrict_restrict, measure_eq_zero_iff_ae_notMem and ae_restrict_iff';
- ContinuousLinearMap.adjoint_inner_left, LinearIsometry.inner_map_map and LinearIndependent.map';
- μHE notation (Geometry/Euclidean/Volume/Measure.lean:72);
- SimonGMT CountablyRectifiable.mono (Rectifiable.lean:55).
No existing project declaration covers the three new lemmas.

Lean checks:
- Children.lean proves the three new children with only propext, Classical.choice and Quot.sound.
- AssemblyInd.lean proves the exact frozen parent type from the 4 children and the 3 sibling contracts, without sorryAx.
- All Lean types are byte-identical to the frozen DAG strings.
- The reused dgce_left_inverse_chart_embedded is accepted (comparator passed), has an identical type, and uses only standard axioms in a fresh compile of b4813988.

Names: codim1_pfr_* appears in no DAG node and on none of the 1828 git ref tips.
