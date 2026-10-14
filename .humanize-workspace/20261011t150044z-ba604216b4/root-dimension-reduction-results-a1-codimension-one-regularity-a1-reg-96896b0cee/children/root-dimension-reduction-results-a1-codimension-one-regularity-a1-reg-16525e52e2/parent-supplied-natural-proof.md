# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.flat_tangent_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.flat_tangent_density-a1.test_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. The lower half of parent Step 2, "I_r(f₋) ≤ r^{-m} μ(B_r(y))" (from f₋ ≤ 1_{B_1}), isolated as a lemma about an arbitrary set A outside which the test function vanishes, and combined with the limit I_r → L > L'. No finiteness of μ and no compact support are needed.

Notation. I_r := r^{-m} ∫ f(r^{-1}(z − y)) dμ(z) (Bochner integral), S_r := {z : r^{-1}(z − y) ∈ A}, and g_r(z) := f(r^{-1}(z − y)).

1. Eventual choice. Since I_r → L and (L', ∞) is a neighbourhood of L, eventually along 𝓝[>]0 we have I_r > L'; also eventually r > 0 ((0, ∞) is a member of 𝓝[>]0). Fix r in both sets. Then g_r is continuous (hence measurable), 0 ≤ g_r ≤ 1, and g_r(z) = 0 whenever z ∉ S_r, because then r^{-1}(z − y) ∉ A.

2. From I_r = (r^m)^{-1} ∫ g_r dμ > L' and r^m > 0 we get L' r^m < ∫ g_r dμ, hence ofReal(L' r^m) ≤ ofReal(∫ g_r dμ).

3. ofReal(∫ g_r dμ) ≤ ∫⁻ ofReal(g_r) dμ. If g_r is μ-integrable this is an equality, since g_r ≥ 0. If g_r is not μ-integrable, the Bochner integral is 0 by definition and ofReal(0) = 0 ≤ ∫⁻ ofReal(g_r) dμ.

4. Pointwise ofReal(g_r(z)) ≤ 1_{S_r}(z): for z ∈ S_r, ofReal(g_r(z)) ≤ ofReal(1) = 1; for z ∉ S_r, g_r(z) = 0. Hence ∫⁻ ofReal(g_r) dμ ≤ ∫⁻ 1_{S_r} dμ ≤ μ(S_r); the last inequality holds for an arbitrary (not necessarily measurable) set S_r.

5. Conclusion. Chaining 2–4: ofReal(L' r^m) ≤ ofReal(∫ g_r dμ) ≤ ∫⁻ ofReal(g_r) dμ ≤ μ(S_r). This holds for every r in an 𝓝[>]0-eventual set. ∎

Formalization notes (compiled in this session after import GMT.Ch07.Submission, /tmp/ftd3-check/Full.lean): filter_upwards [hlim (Ioi_mem_nhds hLL'), self_mem_nhdsWithin]; lt_inv_mul_iff₀ (pow_pos hr m); by_cases on Integrable, using ofReal_integral_eq_lintegral_ofReal or integral_undef with ENNReal.ofReal_zero and `exact zero_le` (no explicit argument in this Mathlib); lintegral_mono with indicator_of_mem / indicator_of_notMem, a `show ENNReal.ofReal (f (r⁻¹ • (z - y))) ≤ …` to beta-reduce, and lintegral_indicator_one_le.

## Key steps

1. Eventually r > 0 and I_r > L', so L' r^m < ∫ g_r dμ.
2. ofReal(∫ g_r dμ) ≤ ∫⁻ ofReal g_r dμ (equality if integrable; otherwise the Bochner integral is 0).
3. ofReal ∘ g_r ≤ 1_{S_r} pointwise, so ∫⁻ ofReal g_r dμ ≤ μ(S_r).

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean <snapshot>/project/GMT/Ch07/Contract.lean`
- `cmp <snapshot>/mathlib/<f> .lake/packages/mathlib/<f> for 14 cited Mathlib files (Geometry/Euclidean/Volume/Measure, Lebesgue/EqHaar, Bochner/{Basic,Set}, Lebesgue/{Markov,Basic}, IntegrableOn, MetricSpace/HausdorffDistance, Instances/ENNReal/Lemmas, InnerProductSpace/{Projection/FiniteDimensional,Orthogonal,Basic}, Basic/ENNReal/{Inv,Basic}): all identical`
- `rg -n "theorem (Isometry\.euclideanHausdorffMeasure_image|EuclideanSpace\.euclideanHausdorffMeasure_eq_volume|addHaar_ball_of_pos|IntegrableOn\.of_forall_sdiff_eq_zero|integral_mono_of_nonneg|integral_undef|integral_indicator_const|mem_orthogonal_singleton_iff_inner_left|abs_real_inner_le_norm|infDist_zero_of_mem|div_le_of_le_mul|lt_iff_exists_real_btwn|mul_meas_ge_le_lintegral₀|ofReal_integral_eq_lintegral_ofReal|lintegral_indicator_one_le|finrank_orthogonal_span_singleton|tendsto_nhds_zero|infDist_lt_iff)\b" <snapshot>/mathlib/Mathlib`
- `grep -n "μHE\|notation\|euclideanHausdorffMeasure_image" <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; sed -n 440,452p <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `python3 scans of dag.json: target node (status decomposing, 'subproblem decomposition attempt 3', children []); lean_name reservations matching ftd|flat_tangent|subspace_ball|plane_ball|rdo_dg; status/candidate_commit of codim1_subspace_ball_euclideanHausdorff (accepted, 6fadc8de) and idtp_tdc_subspace_ball_measure (accepted, a029156d); collision check of the five fresh names (0 hits)`
- `rg/grep -rn codim1_rdo_dg_ftd_ over GMT, .lake/packages/simongmt, <snapshot>, run-directory JSON (only this node's decomposition-v1/v2 drafts); git log --all --oneline -S codim1_rdo_dg_ftd_ (no commits)`
- `sed -n runtime.py _existing_lean_name_problem/_accepted_checkpoint/_decompose/_reference_use_problem and models.py Subproblem/Decomposition/ScopedDecomposition (live flow gmt-claude-9a0895c8c5e1); swarm-project.json (max_depth 6, max_children 12)`
- `sed -n 85,110p book/chapter-03.txt (Simon Ch. 3, Remark 1.5(3)); cat this node's parent-child-handoff.json, parent-supplied-plan.md, decomposition-v1.json, decomposition-v2.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json`
- `lake env lean -DautoImplicit=false /tmp/ftd3-check/Types.lean (5 child types + exact parent assembly; sorry warnings only)`
- `lake env lean -DautoImplicit=false /tmp/ftd3-check/Full.lean (complete proofs of all children + parent; #print axioms = [propext, Classical.choice, Quot.sound])`
- `lake env lean -DautoImplicit=false /tmp/ftd3-check/Inst.lean (instance audit: BorelSpace (Euclid N), unitBallVolume rfl, inner product and smul coordinatewise, pp.explicit of μHE[m])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96896b0cee/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96896b0cee/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96896b0cee/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96896b0cee/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/tmp/ftd3-check/Types.lean`
- `/tmp/ftd3-check/Full.lean`
- `/tmp/ftd3-check/Inst.lean`

Pins match: snapshot manifest project b4d606db / Mathlib 25730c7c equal workspace HEAD and .lake/packages/mathlib (simongmt 2b366308); snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…); the 14 cited Mathlib files are byte-identical to the snapshot. The snapshot supplies every library fact the children use: Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:131,187), Measure.addHaar_ball_of_pos (Lebesgue/EqHaar.lean:445), mul_meas_ge_le_lintegral₀ (Lebesgue/Markov.lean:52), ofReal_integral_eq_lintegral_ofReal and integral_undef (Bochner/Basic.lean), lintegral_indicator_one_le (Lebesgue/Basic.lean:563), IntegrableOn.of_forall_sdiff_eq_zero, infDist_lt_iff (HausdorffDistance.lean:513), ENNReal.tendsto_nhds_zero (ENNReal/Lemmas.lean:237), finrank_orthogonal_span_singleton (Projection/FiniteDimensional.lean:125). No snapshot declaration states the parent or any child, so none can be reused. Two plane-ball lemmas exist in other branches (codim1_subspace_ball_euclideanHausdorff, idtp_tdc_subspace_ball_measure). Per the correction, neither is reused: the plane-ball child gets the fresh name codim1_rdo_dg_ftd_plane_ball_measure. All five fresh names have 0 hits in the 1194-node DAG, GMT/, SimonGMT, the snapshot and the git history. Lean checks: Types.lean elaborates all five child types and proves the exact frozen parent type from them; Full.lean proves all five children and the parent sorry-free with axioms [propext, Classical.choice, Quot.sound]; Inst.lean confirms the Euclidean/Borel instances behind μHE[m], μ, unitBallVolume and inner.
