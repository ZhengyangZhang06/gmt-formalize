# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1`
- Child DAG node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1.plane_ball_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent proof ('H(T.plane ∩ B_1(0)) = ω because H(J(E)) = vol_n(E) ... and T.plane ∩ B_1(0) = J(B_1(0))'), stated for any radius r > 0. H := μHE[n].
1. The map y ↦ (y,T) is measurable and B_r(0) × G is measurable. Measure.map_apply and then Measure.restrict_apply give
   v(T)(B_r(0) × G) = (H⌞T.plane)({y : (y,T) ∈ B_r(0) × G}) = H(B_r(0) ∩ T.plane),
   because {y : (y,T) ∈ B_r(0) × G} = B_r(0).
2. Let e : ℝ^n ≃ T.plane be a linear isometric equivalence, built from an orthonormal basis of T.plane indexed by Fin n (finrank T.plane = n, Grassmannian.finrank_plane). Let J(x) := (e x : ℝ^N). Then J is an isometry, since |J x − J x'| = |e(x − x')| = |x − x'|, and range J = T.plane.
3. For an isometry J, H(J⁻¹(S)) = H(S ∩ range J) (Isometry.euclideanHausdorffMeasure_preimage). With S = B_r(0) this gives H(B_r(0) ∩ T.plane) = H(J⁻¹(B_r(0))). Also J⁻¹(B_r(0)) = B_r(0) ⊆ ℝ^n, because |J x| = |x|.
4. On ℝ^n = EuclideanSpace ℝ (Fin n), μHE[n] equals Lebesgue measure (EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
5. vol(B_r(0)) = ofReal(r^{finrank}) · vol(B°_1(0)) for r ≥ 0 (Measure.addHaar_closedBall, which needs no nontriviality, so n = 0 is included). finrank ℝ (EuclideanSpace ℝ (Fin n)) = n (finrank_euclideanSpace_fin), and vol(B°_1(0)) = ω by definition.
6. ofReal(r^n) = ofReal(r)^n for r ≥ 0 (ENNReal.ofReal_pow). Combining steps 1–6, v(T)(B_r(0) × G) = ofReal(r)^n · ω = ω · ofReal(r)^n. ∎

## Key steps

1. v(T)(B_r(0)×G) = H^n(B_r(0) ∩ T) by map_apply and restrict_apply.
2. A linear isometry J : ℝ^n → ℝ^N with range T transfers H^n(B_r(0) ∩ T) to H^n(B_r(0)) in ℝ^n.
3. H^n is Lebesgue measure on ℝ^n, and vol(B_r(0)) = r^n·ω (addHaar_closedBall, valid also for n = 0).

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
