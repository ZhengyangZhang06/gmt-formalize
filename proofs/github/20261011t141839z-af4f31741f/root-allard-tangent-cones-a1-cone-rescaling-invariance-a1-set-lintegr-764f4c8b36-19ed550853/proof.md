# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1`
- Child DAG node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1.set_lintegral_congr_off_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Step 6, parts (6b) and (6c), in abstract form. G plays the role of M_s, D and D' play the roles of D_A and D'_A, and f and g are the two integrands. The parent text reads: "Measure.restrict_congr_set holds for arbitrary sets … M_s is H-null-measurable … So there is a Borel Z ⊆ M_s with H(M_s ∖ Z) = 0 … ρ(Zᶜ) = H(Zᶜ ∩ …) ≤ H(M_s ∖ Z) = 0, by Measure.restrict_apply since Zᶜ is measurable … lintegral_congr_ae gives equal integrals".

Hypotheses: G is μ-null-measurable; μ(D ∖ G) = 0 and μ(D' ∖ G) = 0; x ∈ D ↔ x ∈ D' for x ∈ G; f x = g x for x ∈ G. The sets D, D' and the functions f, g are otherwise arbitrary.

1. D =ᵐ[μ] D'. If x ∈ D ∖ D', then x ∉ G, since otherwise x ∈ D' by the agreement hypothesis. So D ∖ D' ⊆ D ∖ G and μ(D ∖ D') = 0 (measure_mono_null). Symmetrically, D' ∖ D ⊆ D' ∖ G, so μ(D' ∖ D) = 0. By ae_eq_set, D =ᵐ[μ] D'. Hence μ.restrict D = μ.restrict D' (Measure.restrict_congr_set, valid for arbitrary sets).

2. Measurable kernel of G. By NullMeasurableSet.exists_measurable_subset_ae_eq there is a measurable Z ⊆ G with Z =ᵐ[μ] G. By ae_eq_set, μ(G ∖ Z) = 0.

3. Zᶜ is (μ.restrict D)-null. Since Zᶜ is measurable, (μ.restrict D)(Zᶜ) = μ(Zᶜ ∩ D) (Measure.restrict_apply; D may be arbitrary). Take x ∈ D with x ∉ Z. Either x ∉ G, and then x ∈ D ∖ G, or x ∈ G, and then x ∈ G ∖ Z. Hence Zᶜ ∩ D ⊆ (D ∖ G) ∪ (G ∖ Z). This union is μ-null by the hypothesis, step 2 and measure_union_null. So (μ.restrict D)(Zᶜ) = 0 (measure_mono_null).

4. f =ᵐ[μ.restrict D] g. If f x ≠ g x then x ∉ Z, because x ∈ Z ⊆ G would force f x = g x. So {x | f x ≠ g x} ⊆ Zᶜ, and by step 3 and measure_mono_null this set has (μ.restrict D)-measure 0. That is f =ᵐ[μ.restrict D] g (unfold Filter.EventuallyEq and use ae_iff).

5. Conclusion. ∫⁻_D f dμ = ∫⁻_D g dμ by lintegral_congr_ae and step 4. Then ∫⁻_D g dμ = ∫⁻_{D'} g dμ because μ.restrict D = μ.restrict D' (step 1). ∎

Remark (not a proof step): Mathlib's setLIntegral_congr_fun_ae₀ would need D itself to be null-measurable. In the intended application D is a projection-type set {x ∈ M : ∃ T, …} that is not known to be measurable, and H^n is not s-finite. That is why the a.e. comparison is made against the measurable kernel Z of G.

## Key steps

1. D ∖ D' ⊆ D ∖ G and D' ∖ D ⊆ D' ∖ G, so D =ᵐ D' and μ.restrict D = μ.restrict D' (restrict_congr_set).
2. Choose a measurable Z ⊆ G with μ(G ∖ Z) = 0.
3. (μ.restrict D)(Zᶜ) = μ(Zᶜ ∩ D) ≤ μ(D∖G) + μ(G∖Z) = 0 (restrict_apply on the measurable set Zᶜ).
4. {f ≠ g} ⊆ Zᶜ, so f = g (μ.restrict D)-a.e.
5. lintegral_congr_ae, then rewrite with restrict_congr_set.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (project_commit 63436ae6, mathlib_commit 25730c7c); sha256sum snapshot project/GMT/Ch08/Contract.lean vs workspace GMT/Ch08/Contract.lean and Submission.lean (all 2e5cd5b3…c487)`
- `cat nodes/root-allard-tangent-cones-a1-cone-rescaling-invariance-a1/parent-child-handoff.json and parent-supplied-plan.md; problem.md`
- `grep -n 'IsVarifoldOf|HasTangentPlane|rescaledMeasure|planeVarifoldMeasure' GMT/Ch08/Contract.lean`
- `python3 dump of dag.json nodes (root.allard_tangent_cones-a1 subtree: lean_name, lean_statement, depends_on; sibling tangent_plane_dilation-a1 statement)`
- `grep -rn 'allard_tc_cri' dag.json GMT/ .humanize/ and .swarm-worktrees (*.lean, *.json): no matches`
- `grep '^structure|weight|weight_apply' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `grep 'euclideanHausdorffMeasure_smul₀|homothety' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep 'restrict_map|restrict_congr_set|restrict_apply|restrict_apply₀'|restrict_eq_zero|exists_measurable_subset_ae_eq|lintegral_map_equiv|lintegral_eq_zero_iff'|setLIntegral_measure_zero' mathlib/Mathlib/MeasureTheory`
- `grep 'def smul₀|preimage_smul₀|mem_inv_smul_set_iff₀|MeasurableSet.const_smul' mathlib/Mathlib`
- `rg 'theorem (lintegral_comp_smul|setLIntegral_congr|setLIntegral_congr_fun)' mathlib/Mathlib/MeasureTheory; rg lintegral in Hausdorff.lean and Volume/Measure.lean`
- `rg 'euclideanHausdorffMeasure_smul₀|MeasurableEquiv.smul₀|lintegral_map_equiv' and '^theorem .*(rescal|dilat|homothety)' over SimonGMT`
- `contract_scope(Contract.lean, 'GMT.Ch08.main_theorem') from verifier/gmt-compare.py; validate_lean_statement from verifier/lean_contract.py on the 4 child statements`
- `lake env lean /tmp/cri-decomp/{Stmts,ChildAC,ChildB,All,Cmp}.lean (import GMT.Ch08.Submission + replayed scope, autoImplicit false; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-cone-rescaling-invariance-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-cone-rescaling-invariance-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Group/MeasurableEquiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/GroupWithZero/Action/Pointwise/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Group/Pointwise.lean`
- `/tmp/cri-decomp/Stmts.lean`
- `/tmp/cri-decomp/ChildAC.lean`
- `/tmp/cri-decomp/ChildB.lean`
- `/tmp/cri-decomp/All.lean`
- `/tmp/cri-decomp/Cmp.lean`
- `/tmp/cri-decomp/stmts.json`

The snapshot pins project 63436ae6 and Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract and Submission.

What the snapshot already provides:
- Varifold.weight = measure.map Prod.fst, with weight_apply on measurable sets (SimonGMT Chapter08/Varifold.lean).
- Mathlib lemmas valid for arbitrary sets and functions, with no σ-finiteness: Measure.euclideanHausdorffMeasure_smul₀ (μHE[d](r•s) = ‖r‖₊^d•μHE[d] s for every s), MeasurableEquiv.smul₀ / coe_smul₀, Set.preimage_smul₀, Set.mem_inv_smul_set_iff₀, MeasurableEquiv.restrict_map, lintegral_map_equiv, Measure.restrict_congr_set and Measure.restrict_apply (measurable test set, arbitrary restricting set).
- Also present: NullMeasurableSet.exists_measurable_subset_ae_eq, lintegral_eq_zero_iff', setLIntegral_measure_zero and Measure.restrict_eq_zero.

What is missing (no match in Mathlib or SimonGMT):
- No change-of-variables lintegral lemma for Hausdorff measure under dilations. SimonGMT has only simonHausdorffMeasure_smul, a wrapper of the set-level Mathlib lemma.
- No varifold rescaling-of-representation lemma.
- No carrier dilation-invariance lemma.
- Mathlib's setLIntegral_congr_fun_ae₀ needs a null-measurable integration set, so it does not cover child C.

The pinned Mathlib deprecates Set.mem_setOf_eq (use Set.mem_ofPred_eq) and Set.diff_eq (use Set.sdiff_eq).

Scratch checks: all 4 child statements validate and elaborate in the replayed comparator scope, and each is fully proved with only propext, Classical.choice and Quot.sound. The frozen parent type is closed using only the 4 children and the verbatim sibling allard_tc_tangent_plane_dilation interface.
