# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.interior_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part I.1 of the selected node's proof (the interior product ♭_g with a frame and the test forms ♭_gω(t + ·)). Here the frame is arbitrary (orthonormality is not needed for (a)), the bound ‖♭‖ ≤ 1 is not claimed, and (b) is stated for an arbitrary continuous linear Φ between covector spaces, so that it also applies to the identity map and to the maps of (a).
Notation: for v : Fin m → ℝ^P write ṽ := Fin.append g v ∘ Fin.cast h : Fin n' → ℝ^P. By Fin.append_left and Fin.append_right, ṽ(l) = g_i if Fin.cast h l = Fin.castAdd m i, and ṽ(l) = v_j if Fin.cast h l = Fin.natAdd k j. For j : Fin m put ι_j := Fin.cast h.symm (Fin.natAdd k j) : Fin n'; the map j ↦ ι_j is injective (Fin.natAdd and Fin.cast are injective).
Part (a).
1. (Updates.) For j : Fin m, v : Fin m → ℝ^P and x ∈ ℝ^P: Fin.append g (Function.update v j x) ∘ Fin.cast h = Function.update ṽ ι_j x. Evaluate both sides at l : Fin n' and split Fin.cast h l with Fin.addCases. If Fin.cast h l = Fin.castAdd m i, both sides equal g_i (and l ≠ ι_j). If Fin.cast h l = Fin.natAdd k j', both sides equal (Function.update v j x)(j'), because l = ι_j exactly when j' = j.
2. (Multilinearity.) Fix α ∈ Λ^{n'} and put φ_α(v) := α(ṽ). By step 1 and the multilinearity of α in the slot ι_j (map_update_add, map_update_smul): φ_α(update v j (x + x')) = φ_α(update v j x) + φ_α(update v j x') and φ_α(update v j (c·x)) = c·φ_α(update v j x).
3. (Alternation.) If v_j = v_{j'} for some j ≠ j', then ṽ(ι_j) = v_j = v_{j'} = ṽ(ι_{j'}) with ι_j ≠ ι_{j'}, so φ_α(v) = α(ṽ) = 0 because α is alternating (map_eq_zero_of_eq).
4. (Continuity and bound.) v ↦ ṽ is continuous (every coordinate is either a constant g_i or a coordinate projection v ↦ v_j) and α is continuous, so φ_α is continuous; hence φ_α ∈ Λ^m. Moreover |φ_α(v)| ≤ ‖α‖·∏_{l : Fin n'} ‖ṽ(l)‖ = ‖α‖·(∏_i ‖g_i‖)·(∏_j ‖v_j‖) (ContinuousMultilinearMap.le_opNorm; reindex the product over Fin n' along Fin.cast h and split it with Fin.prod_univ_add). Hence ‖φ_α‖ ≤ C·‖α‖ with C := ∏_i ‖g_i‖ (ContinuousMultilinearMap.opNorm_le_bound).
5. (Linearity in α.) φ_{α+β} = φ_α + φ_β and φ_{c·α} = c·φ_α (ext: evaluate both sides at v). By step 5 and the bound of step 4, LinearMap.mkContinuous yields a continuous linear map ♭ : Λ^{n'} → Λ^m with ♭α = φ_α; by construction (♭α)(v) = α(Fin.append g v ∘ Fin.cast h). (Alternatively: Λ^{n'} is finite-dimensional, so every linear map out of it is continuous.)
Part (b).
6. (Smoothness.) y ↦ Φ(ω(t + y)) is the composite of the smooth map y ↦ t + y, the C^∞ map ω and the continuous linear map Φ; hence it is C^∞ (ContDiff.comp, ContinuousLinearMap.contDiff, contDiff_const.add contDiff_id).
7. (Support.) If t + y ∉ support ω then Φ(ω(t + y)) = Φ(0) = 0; so support(y ↦ Φ(ω(t + y))) ⊆ (t + ·)⁻¹'(tsupport ω). The right side is closed (the preimage of a closed set under a continuous map), so it also contains the closure of the support: tsupport(y ↦ Φ(ω(t + y))) ⊆ (t + ·)⁻¹'(tsupport ω) = {y : t + y ∈ tsupport ω}.
8. (Compact support.) (t + ·)⁻¹'(tsupport ω) is the image of the compact set tsupport ω under the continuous map z ↦ z − t, hence compact; tsupport(y ↦ Φ(ω(t + y))) is a closed subset of it, hence compact, i.e. y ↦ Φ(ω(t + y)) has compact support. With step 6, IsTestForm (y ↦ Φ(ω(t + y))) holds. ∎

## Key steps

1. Updating one entry of v updates exactly one entry of Fin.append g v ∘ Fin.cast h, so v ↦ α(Fin.append g v ∘ Fin.cast h) is multilinear, alternating (equal entries stay at distinct indices) and continuous: an element of Λ^m.
2. α ↦ that element is linear and bounded by (∏‖g_i‖)·‖α‖, so LinearMap.mkContinuous gives the continuous linear ♭ with the defining identity.
3. Φ ∘ ω ∘ (t + ·) is smooth and vanishes off the compact set (t + ·)⁻¹'(tsupport ω), so it is a test form with the stated tsupport bound.

## Reference use

### local-project

Queries:
- `cat manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 over dag.json: split_off_spine nodes and statuses; ancestors and their depends_on; all 2101 accepted nodes dumped to /tmp/mt-decomp/accepted.txt and grepped for translate|massOn_le_add|measure_restrict|support|blowUp|hasDerivAt`
- `git show <candidate>:GMT/Ch07/Submission.lean for idtp_fons_cs_sos_product_current (4aa9ba8d), lcmp_massOn_le_add_of_eval_eq (c7dea4b8), dimred_cs_ti_translate_action_hasDerivAt (f899c748): declarations present, types byte-identical; product_current adds import Poincare.SimonGMT.Chapter02.AreaLipschitz`
- `read nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-60772a06fe/parent-supplied-natural-proof.md (parallel minimality_transfer with the identical frozen type, product construction moved to product_current) and the accepted proofs of the three reused nodes`
- `grep -n over runtime.py (_dependency_problem, _existing_lean_name_problem, _overlay_accepted_children) and inherited.py (cited_inherited: ancestor dependencies cited by exact Lean name)`
- `grep -n over SimonGMT Chapter06/{Currents,Mass,Forms,CurrentLocalEquality}.lean and Chapter03/Rectifiable.lean: GeometricCurrentOn.boundary(_apply), exteriorDerivativeTestOn, CurrentOn.boundary_boundary, massOn/mass/massOn_mono, zeroRegion/support, exteriorDerivative_apply, CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt`
- `grep -n over snapshot mathlib Geometry/Euclidean/Volume/Measure.lean: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, IsometryEquiv.measurePreserving_euclideanHausdorffMeasure`
- `rg -n over snapshot mathlib: PiLp.volume_preserving_toLp, Real.volume_pi_closedBall, Real.volume_pi_ball, measurePreserving_piFinSuccAbove, intervalIntegral.integral_eq_sub_of_hasDerivAt, continuousAt_of_dominated, setIntegral_sdiff (integral_diff deprecated alias), measure_add_measure_compl, withDensity_apply, Measure.restrict_restrict, Measure.integrableOn_of_bounded, Fin.append_left, fderiv_comp_add_left, finrank_span_eq_card, Submodule.eq_of_le_of_finrank_eq, ENNReal.le_of_add_le_add_left, lintegral_indicator_const, Fin.removeNth`
- `rg -n "Cartesian product of currents|slice of a current|cartesianProduct" snapshot mathlib (no match)`
- `lake env lean /tmp/mt-decomp/check/{Types,Assembly,CubeCycle,CompMass}.lean (Lean v4.35.0-rc3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-60772a06fe/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-da13543666/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-triangle-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-inv-37aaf335d9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/mt-decomp/check/Types.lean`
- `/tmp/mt-decomp/check/Assembly.lean`
- `/tmp/mt-decomp/check/CubeCycle.lean`
- `/tmp/mt-decomp/check/CompMass.lean`

Pins match. The snapshot manifest records project b4d606db1 (= workspace HEAD) and mathlib 25730c7c; the snapshot Contract.lean equals the workspace Contract.lean and Submission.lean.

Library gaps. Simon leaves Lemma 7.3.5 to the reader (book/chapter-07.txt), so the supplied proof is the project's own argument. SimonGMT has:
- no general Cartesian products of currents;
- no slicing;
- no translation lemma for currents.
Snapshot mathlib has no currents at all ("Cartesian product of currents|slice of a current": no match).

Accepted reuse. dag.json has 2101 accepted declarations. Three fit this proof with byte-identical frozen types, present in their candidate commits:
- idtp_fons_cs_sos_product_current (4aa9ba8d): exactly the I.3 product construction; it also carries the AreaLipschitz import;
- lcmp_massOn_le_add_of_eval_eq (c7dea4b8): the mass triangle inequality;
- dimred_cs_ti_translate_action_hasDerivAt (f899c748): the derivative of s ↦ R.action(ω(sv + ·)).
These are reused as children. Inherited by exact-name citation (inherited.py): dtc_imrep_current, imrep_represents_massOn_eq_measure, imrep_carrier_sdiff_support_null, rsd_isIntegerMultiplicity_int_combination and dimred_im_mass_measure.

Mathlib facts the child proofs need are present in the snapshot, among them:
- μHE[k] = volume on EuclideanSpace and the isometry push-forward Isometry.map_euclideanHausdorffMeasure;
- PiLp.volume_preserving_toLp, Real.volume_pi_closedBall / volume_pi_ball and measurePreserving_piFinSuccAbove;
- the FTC integral_eq_sub_of_hasDerivAt, continuousAt_of_dominated and setIntegral_sdiff;
- finrank_span_eq_card and Submodule.eq_of_le_of_finrank_eq;
- SimonGMT exteriorDerivative_apply, GeometricCurrentOn.boundary_apply and the CountablyRectifiable / HasApproximateTangentSpaceAt definitions via blowUpMap images.

Lean checks. All 12 child types elaborate. The parent's frozen type compiles from the child stubs and its own dependency stubs (axioms: propext, sorryAx from stubs only, Classical.choice, Quot.sound). Skeletons of cube_cycle and competitor_mass compile against their sibling stubs. The runtime gates (ScopedDecomposition validation, _dependency_problem, _existing_lean_name_problem) pass on dag.json. The parallel node idtp_fons_cs_sos_minimality_transfer has the identical frozen type but is not accepted, so it is not reused.
