# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1`
- Child DAG node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1.rescaled_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Step 5 (B6), with the tangent-plane condition replaced by an arbitrary relation P and θ by an arbitrary density g. The parent text reads: "Φ(z,S) := (s⁻¹•(z − 0), S) is continuous, so A' := Φ⁻¹(A) is Borel. By Measure.smul_apply and Measure.map_apply, rescaledMeasure C 0 s A = ofReal(s⁻¹^n)·C.measure(A'). By (★), C.measure(A') = ∫⁻_{D_{A'}} … ; … ∫⁻_{D_{A'}} … = ofReal(s)^n·∫⁻_{D'_A} … because s⁻¹•(s•w) = w. Since ofReal(s⁻¹^n)·ofReal(s)^n = 1 …". Uses the sibling child hausdorff_dilation_lintegral (Lean: Submission.allard_tc_cri_hausdorff_dilation_lintegral).

Notation. H := (μHE[n] : Measure (Euclidean N)) and c := ENNReal.ofReal. Call the representation hypothesis (R). Fix s > 0 and a measurable A ⊆ Euclidean N × Grassmannian N n. Put Φ(z) := (s⁻¹ • (z.1 − 0), z.2).

1. Φ is built from the continuous projections, subtraction of the constant 0 and scalar multiplication, so it is continuous and hence measurable (fun_prop, or Continuous.measurable). Therefore A' := Φ⁻¹(A) is measurable.

2. By definition, rescaledMeasure C 0 s = c(s⁻¹^n) • C.measure.map Φ. Hence rescaledMeasure C 0 s A = c(s⁻¹^n) · (C.measure.map Φ)(A) = c(s⁻¹^n) · C.measure(A'). This uses unfolding rescaledMeasure, Measure.smul_apply, smul_eq_mul, and Measure.map_apply with step 1 and the measurability of A.

3. Apply (R) to the measurable set A'. This gives C.measure(A') = ∫⁻_{D₁} g dH, where D₁ := {x | x ∈ M ∧ ∃ T, P x T ∧ (x, T) ∈ A'} = {x | x ∈ M ∧ ∃ T, P x T ∧ (s⁻¹ • (x − 0), T) ∈ A}.

4. Apply the sibling hausdorff_dilation_lintegral with D := D₁ and f := g, i.e. Submission.allard_tc_cri_hausdorff_dilation_lintegral N n s D₁ g hs. This gives ∫⁻_{D₁} g dH = c(s)^n · ∫⁻_{{w | s • w ∈ D₁}} g(s • w) dH(w).

5. Set identity: {w | s • w ∈ D₁} = {w | s • w ∈ M ∧ ∃ T, P (s • w) T ∧ (w, T) ∈ A}. Indeed s • w ∈ D₁ ⟺ s • w ∈ M ∧ ∃ T, P (s • w) T ∧ (s⁻¹ • (s • w − 0), T) ∈ A. Moreover s⁻¹ • (s • w − 0) = s⁻¹ • (s • w) = w by sub_zero and inv_smul_smul₀ (s ≠ 0). In Lean: Set.ext, then simp only [Set.mem_ofPred_eq (or the deprecated Set.mem_setOf_eq), Set.mem_preimage, sub_zero, inv_smul_smul₀ hs.ne'].

6. The constant is 1: c(s⁻¹^n) · c(s)^n = c(s⁻¹)^n · c(s)^n = (c(s⁻¹) · c(s))^n = c(s⁻¹ · s)^n = c(1)^n = 1. This uses ENNReal.ofReal_pow (s⁻¹ ≥ 0), mul_pow, ENNReal.ofReal_mul (s⁻¹ ≥ 0), inv_mul_cancel₀, ENNReal.ofReal_one and one_pow.

7. Combine steps 2–6 with mul_assoc and one_mul: rescaledMeasure C 0 s A = c(s⁻¹^n) · (c(s)^n · ∫⁻_{S} g(s • w) dH(w)) = ∫⁻_{S} g(s • w) dH(w), where S = {w | s • w ∈ M ∧ ∃ T, P (s • w) T ∧ (w, T) ∈ A}. This is the claim. ∎

## Key steps

1. Φ(z) = (s⁻¹•(z.1−0), z.2) is continuous, so A' = Φ⁻¹A is measurable.
2. rescaledMeasure C 0 s A = ofReal(s⁻¹^n)·C.measure(A') (Measure.smul_apply, Measure.map_apply).
3. The representation at A' gives ∫⁻ over {x∈M : ∃T, P x T ∧ (s⁻¹•(x−0),T)∈A} of g dH.
4. Change variables with hausdorff_dilation_lintegral: a factor ofReal(s)^n and the set {w | s•w ∈ D₁}.
5. Simplify the set via s⁻¹•(s•w − 0) = w.
6. ofReal(s⁻¹^n)·ofReal(s)^n = 1.

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
