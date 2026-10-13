# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.pushforward_rep-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.pushforward_rep-a1.normal_field_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 4 of the parent proof: the field ξ̃ and its Borel measurability, for an arbitrary map G and a Borel ν. The parent applies it with G(y) := x + ιy + u(y).
Notation.
- E := ℝ^P.
- Cov := Covector(E, n) = E [⋀^Fin n]→L[ℝ] ℝ, the continuous alternating n-linear forms on E.
- Λ := MultiVector P n = Cov →L[ℝ] ℝ.
- Cov and Λ carry the operator norm.
- DG(v) := fderiv ℝ G v; Mathlib sets it to 0 where G is not differentiable.
- e_j := EuclideanSpace.single j 1.
1. (Evaluation.) For b = (b_0, …, b_{n−1}) ∈ E^n let ev(b) : Cov → ℝ, ev(b)(α) := α(b).
- ev(b) is linear in α, and |α(b)| ≤ ‖α‖·Π_k‖b_k‖, so ev(b) ∈ Λ.
- The map ev : E^n → Λ is the continuous alternating map ContinuousLinearMap.flipAlternating applied to the identity of Cov.
- By definition (flipAlternating_apply_apply; it holds by rfl), ev(b)(α) = α(b) for all b and α.
- In particular ev is continuous (ContinuousAlternatingMap.coe_continuous).
2. (The frames.) For j ∈ Fin(n+1) define b_j : ℝ^{n+1} → E^n by b_j(v) := (k ↦ DG(v)e_{j.succAbove k}).
- For each fixed vector y, v ↦ DG(v)y is Borel for every map G (measurable_fderiv_apply_const; E is complete).
- A map into the finite product E^n is Borel iff each coordinate is (measurable_pi_iff), so b_j is Borel.
- E^n is second countable and metrizable, so b_j is strongly measurable (Measurable.stronglyMeasurable).
- Since ev is continuous, ev∘b_j is strongly measurable (Continuous.comp_stronglyMeasurable).
3. (The coefficients.) c_j(v) := (−1)^j·⟨e_j, ν(v)⟩ is Borel.
- w ↦ ⟨e_j, w⟩ is continuous (Continuous.inner) and ν is Borel, so v ↦ ⟨e_j, ν(v)⟩ is Borel.
- Multiplying by the constant (−1)^j keeps it Borel (measurable_const.mul).
- Hence c_j is a strongly measurable real function.
4. (Definition and measurability.) Put ξ̃(v) := −Σ_{j=0}^{n} c_j(v)•ev(b_j(v)).
- Each summand v ↦ c_j(v)•ev(b_j(v)) is strongly measurable (StronglyMeasurable.smul, by continuity of scalar multiplication ℝ × Λ → Λ).
- The finite sum s(v) := Σ_j c_j(v)•ev(b_j(v)) is strongly measurable (Finset.stronglyMeasurable_fun_sum).
- So is its negative −s, which is v ↦ −s(v) by definition (StronglyMeasurable.neg). This is ξ̃.
- The last two lemmas need ContinuousAdd Λ and ContinuousNeg Λ. Both hold because Λ is a normed, hence topological, additive group.
- In Lean, instance search fails for MultiVector P n ('failed to synthesize ContinuousAdd (MultiVector P n)'). Introduce them as local instances before the measurability argument, as (inferInstance : IsTopologicalAddGroup (MultiVector P n)).toContinuousAdd and (inferInstance : IsTopologicalAddGroup (MultiVector P n)).toContinuousNeg.
5. (The formula.) Fix v and α. Evaluation at α is additive and homogeneous on Λ (neg_apply, sum_apply, smul_apply, smul_eq_mul), so
 ξ̃(v)(α) = −Σ_j c_j(v)·ev(b_j(v))(α) = −Σ_j (−1)^j·⟨e_j, ν(v)⟩·α(b_j(v)).
 Commuting the real factors in each summand (Finset.sum_congr and ring) gives
 −Σ_j (−1)^j·α(DG(v)e_{j.succAbove 0}, …, DG(v)e_{j.succAbove(n−1)})·⟨e_j, ν(v)⟩,
 which is the asserted identity.
6. Steps 4 and 5 give the required ξ̃. ∎

## Key steps

1. ev(b)(α) := α(b) defines a continuous alternating map ev : (ℝ^P)^n → Λ_n(ℝ^P), namely flipAlternating of the identity of Covector(ℝ^P, n).
2. b_j(v) := (DG(v)e_{j.succAbove k})_k is Borel by measurable_fderiv_apply_const and measurable_pi_iff, hence strongly measurable, and so is ev∘b_j.
3. c_j(v) := (−1)^j⟨e_j, ν(v)⟩ is Borel because ν is Borel and the inner product is continuous.
4. ξ̃ := −Σ_j c_j•(ev∘b_j) is strongly measurable by smul, finite sum and neg. ContinuousAdd and ContinuousNeg on MultiVector P n are supplied as local instances from IsTopologicalAddGroup.
5. Evaluating at α and commuting the real factors gives the required formula.

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
