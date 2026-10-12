# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1`
- Child DAG node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1.constancy_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent proof, printed 'C = θ₀ v(T) by Constancy 4.1'. H := μHE[n] and G := Grassmannian N n.
Imports. Grassmannian.eq_of_plane_eq lives in Poincare.SimonGMT.Chapter08.ConstancyTangent, which GMT.Ch08.Submission does not import yet. Add `import Poincare.SimonGMT.Chapter08.ConstancyTangent`; its axioms are only propext, Classical.choice and Quot.sound.
1. Apply ConstancyTheorem with (N, n, U := univ, V := C, M := T.plane). Its hypotheses hold:
   (a) C.Stationary, by hypothesis.
   (b) IsSimonSubmanifold (E := ℝ^n) 2 T.plane, by sibling subspace_submanifold with P := T.plane. Here finrank T.plane = n (Grassmannian.finrank_plane).
   (c) univ ∩ spt μ_C ⊆ T.plane, since univ ∩ spt μ_C ⊆ spt μ_C ⊆ T.plane.
   (d) T.plane ∩ univ = T.plane is convex (a linear subspace), hence preconnected (Convex.isPreconnected).
   It gives θ ≥ 0 such that, for every measurable A ⊆ ℝ^N × G, C.measure A = ofReal θ · H(E_A), where E_A := {x ∈ T.plane ∩ univ : ∃ S ∈ G, (S.plane : Set ℝ^N) = classicalTangentSpace T.plane x ∧ (x,S) ∈ A}.
2. E_A = {x ∈ T.plane : (x,T) ∈ A}. Let x ∈ T.plane. By sibling subspace_tangent (P := T.plane, y := x), classicalTangentSpace T.plane x = T.plane.
   - If (S.plane : Set) = (T.plane : Set), then S.plane = T.plane (coercion to sets is injective, SetLike.coe_injective), so S = T (SimonGMT Grassmannian.eq_of_plane_eq, ConstancyTangent.lean). Hence (x,T) ∈ A.
   - Conversely, if (x,T) ∈ A, then S := T is a witness.
3. The map y ↦ (y,T) is measurable. So for measurable A, Measure.map_apply and then Measure.restrict_apply (the preimage is measurable) give
   planeVarifoldMeasure T A = (H⌞T.plane)({y : (y,T) ∈ A}) = H({y : (y,T) ∈ A} ∩ T.plane) = H(E_A).
4. By steps 1–3, C.measure A = ofReal θ · planeVarifoldMeasure T A = (ofReal θ • planeVarifoldMeasure T)(A) for every measurable A (Measure.smul_apply). Two measures that agree on measurable sets are equal (Measure.ext), so C.measure = ofReal θ • planeVarifoldMeasure T. ∎

## Key steps

1. Check the four hypotheses of ConstancyTheorem for M = T.plane, U = univ: stationarity, the C² Simon submanifold property (sibling subspace_submanifold), the support inclusion, and convexity hence preconnectedness.
2. The classical tangent space of T.plane is T.plane (sibling subspace_tangent), and S.plane = T.plane forces S = T (Grassmannian.eq_of_plane_eq). So the constancy set is {x ∈ T : (x,T) ∈ A}.
3. That set has H^n-measure v(T)(A) (map_apply, restrict_apply), so C.measure = ofReal θ • v(T) by Measure.ext.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487); git rev-parse HEAD in .lake/packages/simongmt (2b3663083f3fe399b6296fb8eaee52169170e197) and .lake/packages/mathlib (25730c7c)`
- `sed -n 560,640p book/chapter-08.txt (printed proof of 5.5: display (2), (7), (8), Constancy 4.1)`
- `grep -n '^theorem' Chapter08/TangentRadialRigidity.lean Chapter08/ConstancyTangentGraph.lean Chapter08/StationaryMonotonicity.lean`
- `grep -rn 'def project|def plane|def normalProject|theorem continuous_normalProject|theorem eq_of_plane_eq|theorem normalProject_eq_sub|finrank_plane|instance.*CompactSpace' Poincare/SimonGMT`
- `grep 'def IsSimonSubmanifold|def IsSimonLocalRepresentation|def IsProperOnInto' Chapter02/Submanifold.lean`
- `grep 'structure Varifold|def weight|theorem weight_apply|weight_finite_on_compact|def Stationary|def StationaryOn|Stationary.stationaryOn|fst_mem_weight_support_of_mem_support|structure TestVectorField' Chapter08`
- `grep 'mem_support_iff_forall|support_subset_of_isClosed|support_mem_ae' mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `grep 'theorem tendsto_measure_iInter_atTop' mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `grep 'theorem addHaar_closedBall|addHaar_unitClosedBall_eq_addHaar_unitBall|Nontrivial' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `grep 'theorem|notation' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (Isometry.euclideanHausdorffMeasure_image/_preimage, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep 'theorem coe_norm|theorem norm_coe' mathlib/Mathlib/Analysis/Normed/Group/Submodule.lean mathlib/Mathlib/Analysis/Normed/Group/Subgroup.lean`
- `python3 dump of dag.json node ids, lean_names, statuses and statements; grep -c allard_tc_scf dag.json (0); grep -rl allard_tc_scf GMT and the run's nodes/*.json/*.md (none); git log --all -S allard_tc_scf (none)`
- `contract_scope(Contract.lean, 'GMT.Ch08.main_theorem') from verifier/gmt-compare.py and validate_lean_statement from verifier/lean_contract.py (all 8 child types and the parent pass)`
- `lake env lean /tmp/scf-decomp-k7q2/lean/Types.lean (8 child types plus the parent in the replayed scope, autoImplicit false: only sorry warnings)`
- `lake env lean /tmp/scf-decomp-k7q2/lean/Full.lean (sorry-free proofs of the 8 children and the parent assembly, comparator-form targets, #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/scf-decomp-k7q2/lean/{NoExtraImports,Imp4,Imp7,ImpP}.lean (minimal extra imports per child and for the parent)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Normed/Group/Submodule.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Normed/Group/Subgroup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-stationary-cone-flat-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-stationary-cone-flat-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-flat-blowup-ball-limits-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/StationaryMonotonicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/StationaryCutoff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentRadialRigidity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangentGraph.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancySupport.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/tmp/scf-decomp-k7q2/lean/Types.lean`
- `/tmp/scf-decomp-k7q2/lean/Full.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract and Submission, and the pinned SimonGMT is 2b366308. Mathlib supplies the measure-theoretic tools the children cite: Measure.mem_support_iff_forall, Measure.support_subset_of_isClosed, tendsto_measure_iInter_atTop, Measure.addHaar_closedBall (no Nontrivial assumption, so n = 0 needs no special case), Isometry.euclideanHausdorffMeasure_preimage, EuclideanSpace.euclideanHausdorffMeasure_eq_volume and Submodule.norm_coe. SimonGMT supplies Grassmannian.continuous_project, normalProject_eq_sub, eq_of_plane_eq, finrank_plane, Varifold.weight_support_eq_fst_image_support, weight_finite_on_compact, weight_apply and IsSimonSubmanifold/IsSimonLocalRepresentation/IsProperOnInto, all with standard axioms. TangentRadialRigidity proves the zero-defect step only at centre 0 under a constant-ratio hypothesis, so a general-centre child (zero_defect_plane) is needed. No existing comparator-accepted declaration has the type of any proposed child. All 8 child types elaborate in the comparator scope and pass validate_lean_statement. Sorry-free proofs of all children and of the parent assembly compile. The only axioms are propext, Classical.choice and Quot.sound.
