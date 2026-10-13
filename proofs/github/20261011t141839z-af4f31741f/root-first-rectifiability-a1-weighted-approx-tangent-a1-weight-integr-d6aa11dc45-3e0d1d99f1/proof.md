# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.weighted_approx_tangent-a1`
- Child DAG node: `root.first_rectifiability-a1.weighted_approx_tangent-a1.weight_integral_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 of the supplied proof of frt_weighted_approx_tangent (Simon Ch. 8, Thm 1.2, step 7: μ_V restricted to compact pieces is the weighted Hausdorff measure θ H^n⌞M), together with the support reduction ∫_M = ∫_{M ∩ K'} used in its Step 4. Here it is stated for an arbitrary measure μ, a Borel set K and an arbitrary integrand h.

Notation: H := μHE[n]; ν := H.restrict (M ∩ K) (= H⌞(M ∩ K)); ρ(y) := ENNReal.ofReal (θ y) ∈ [0, ∞).

Every integral of a real function is a Bochner integral, which is 0 for non-integrable integrands. Each identity used below holds for arbitrary integrands, so no measurability, boundedness or integrability of h is needed. (In the parent's Step 2 the boundedness and Borel hypotheses on h only served to note that both sides are integrable.)

1. μ.restrict K = ν.withDensity ρ. Two measures on the Borel σ-algebra of ℝ^N are equal as soon as they agree on every Borel set (Measure.ext). Let B be Borel; since K is Borel, so is B ∩ K. Then (μ.restrict K)(B) = μ(B ∩ K) (Measure.restrict_apply, B measurable) = ∫⁻_{(B ∩ K) ∩ M} ρ dH (hypothesis applied to the Borel set B ∩ K). On the other side, (ν.withDensity ρ)(B) = ∫⁻_B ρ dν (withDensity_apply, B measurable) = ∫⁻ ρ d(H.restrict (B ∩ (M ∩ K))) (Measure.restrict_restrict, B measurable). Since (B ∩ K) ∩ M = B ∩ (M ∩ K), the two values are equal.

2. Localization. Because h(z) = 0 for every z ∉ K, h equals its indicator 1_K·h. Hence ∫ h dμ = ∫_K h dμ = ∫ h d(μ.restrict K) (setIntegral_eq_integral_of_forall_compl_eq_zero, which needs no measurability).

3. Density formula. IntegrableOn θ (M ∩ K) H means θ is ν-integrable, so θ is ν-a.e. strongly measurable and hence ν-a.e. measurable. Therefore ρ = ENNReal.ofReal ∘ θ is ν-a.e. measurable (AEMeasurable.ennreal_ofReal), and ρ(y) < ∞ for every y. For such a density, every g : ℝ^N → ℝ satisfies ∫ g d(ν.withDensity ρ) = ∫ ρ(y).toReal · g(y) dν(y) (integral_withDensity_eq_integral_toReal_smul₀). Indeed g is integrable for ν.withDensity ρ iff ρ.toReal·g is integrable for ν, in which case this is the usual density formula; otherwise both sides are 0. Taking g := h and using Step 1: ∫ h d(μ.restrict K) = ∫ ρ(y).toReal · h(y) dν(y).

4. Removing the density. M ∩ K is H-null-measurable, as the intersection of the H-null-measurable set M with the Borel set K. Hence ν-a.e. y lies in M ∩ K (ae_restrict_mem₀). For such y, θ(y) > 0 by hypothesis, so ρ(y).toReal = (ENNReal.ofReal θ(y)).toReal = θ(y) (ENNReal.toReal_ofReal) and ρ(y).toReal · h(y) = h(y) θ(y). By integral_congr_ae, ∫ ρ.toReal · h dν = ∫_{M ∩ K} h(z) θ(z) dH(z).

5. From M ∩ K to M. Put g := h·θ. The set M is the disjoint union of the H-null-measurable sets M ∩ K and M \ K, and g vanishes identically on M \ K because h does. Hence g is integrable on M iff it is integrable on M ∩ K, and in that case ∫_M g dH = ∫_{M ∩ K} g dH + ∫_{M \ K} g dH = ∫_{M ∩ K} g dH. If g is not integrable on either set, both set integrals are 0. Either way ∫_M h θ dH = ∫_{M ∩ K} h θ dH (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero with the null-measurable set M, M ∩ K ⊆ M, and g = 0 on M \ (M ∩ K)).

6. Chaining Steps 2, 3, 4 and 5: ∫ h dμ = ∫ h d(μ.restrict K) = ∫ ρ.toReal · h dν = ∫_{M ∩ K} h θ dH = ∫_M h θ dH. ∎

## Key steps

1. μ.restrict K = (μHE[n].restrict (M ∩ K)).withDensity (ENNReal.ofReal ∘ θ): compare the two measures on each Borel B, using the hypothesis for the Borel set B ∩ K together with withDensity_apply and Measure.restrict_restrict.
2. ∫ h dμ = ∫ h d(μ.restrict K) because h = 0 off K (setIntegral_eq_integral_of_forall_compl_eq_zero).
3. integral_withDensity_eq_integral_toReal_smul₀ (ENNReal.ofReal ∘ θ is a.e. measurable because θ is integrable on M ∩ K, and it is finite): ∫ h d(μ.restrict K) = ∫ (ofReal θ).toReal · h d(H^n⌞(M ∩ K)).
4. A.e. on the null-measurable set M ∩ K, (ofReal θ).toReal = θ since θ > 0 on M; hence the integral equals ∫_{M ∩ K} h θ dH^n.
5. h θ = 0 on M \ K and M is null-measurable, so ∫_{M ∩ K} h θ dH^n = ∫_M h θ dH^n (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero).

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `grep -n 'blowUpMap\|HasWeightedApproximateTangentSpaceAt\|theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; sed -n 85,365p (blowUpMap :96, HasWeightedApproximateTangentSpaceAt :330, HasWeightedApproximateTangentSpaceAt.unique :345)`
- `grep -n 'structure Varifold' -A 40 and 'def weight|weight_finite_on_compact|finrank_plane|ofSubmodule_plane' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean (isOpen_domain :336, weight :557, finrank_plane :126, ofSubmodule_plane :196)`
- `grep -rn 'blowUpMap' / 'HasWeightedApproximateTangentSpaceAt' / 'projectionLinearMap_eq_starProjection' .lake/packages/simongmt/Poincare --include=*.lean (Chapter04/WeightedBlowUp.lean: blowUpHomeomorph :29, map_inverse_blowUp_carrier :45, integral_weighted_blowUp :84; Chapter04/TangentDensity.lean: hausdorff_blowUp_image :31; Chapter08/ConstancyTangent.lean: eq_of_plane_eq :33; Chapter08/RadialFirstVariation.lean :34)`
- `grep -n 'weight_eq_carrier_withDensity' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/*.lean (MultiplicityBridge.lean:32)`
- `python3 -I /tmp/wat_scripts/closure.py .lake/packages/simongmt <Contract imports> (22-module SimonGMT import closure; Chapter04.*, Chapter08.ConstancyTangent and Chapter08.RadialFirstVariation are NOT in it)`
- `sed -n 60,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (Isometry.euclideanHausdorffMeasure_image :131, Measure.euclideanHausdorffMeasure_smul₀ :152, euclideanHausdorffMeasure_homothety_image :164, _preimage :170)`
- `grep -n 'theorem integral_withDensity_eq_integral_toReal_smul₀' mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean (:311)`
- `grep -n 'theorem setIntegral_eq_of_subset_of_ae_sdiff_eq_zero|theorem setIntegral_eq_integral_of_forall_compl_eq_zero' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean (:442, :486)`
- `grep -n 'MeasurableEmbedding.integral_map|theorem integral_smul_measure|theorem integral_congr_ae' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean (:1093, :1052, :301)`
- `grep -n 'theorem restrict_map (μ : Measure α) (s : Set β)|theorem restrict_restrict (hs|theorem restrict_smul|theorem ae_restrict_mem₀' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean (:890, :205, :193, :637)`
- `grep -n 'theorem withDensity_apply (f' mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean (:44); grep -n 'theorem ext (h' mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean (:144)`
- `grep -rn 'AEMeasurable.ennreal_ofReal|Homeomorph.measurableEmbedding|theorem toReal_ofReal ' mathlib/Mathlib (BorelSpace/Real.lean:188, BorelSpace/Basic.lean:567, Basic/ENNReal/Basic.lean:252)`
- `lake env lean /tmp/wat_scratch/Where.lean (#eval getModuleIdxFor?: isometry_add_left in Mathlib.Topology.MetricSpace.IsometricSMul; Grassmannian.ofSubmodule_plane in Poincare.SimonGMT.Chapter08.Varifold)`
- `lake env lean /tmp/wat_scratch/Test1.lean (Chapter03.blowUpMap x r y = r⁻¹ • (y - x) by rfl from the non-module Submission; #check signatures)`
- `lake env lean /tmp/wat_scratch/ChildA.lean, ChildB.lean, ChildB2.lean (full proofs of both children; no errors, no warnings)`
- `lake env lean /tmp/wat_scratch/Parent.lean and /tmp/wat_scratch/Final.lean (frozen parent type from both children + sorry'd sibling frt_weight_blowup_tendsto; exact Submission.X targets; #print axioms)`
- `python3 -I /tmp/wat_scripts/gen_nc.py (verifier gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement) then lake env lean /tmp/wat_scratch/nc/<lean_name>/NodeChallenge.lean`
- `python3 -I dag.json scan of 77 nodes: lean_name collision check and search of lean_statements for blowUpMap/withDensity/weighted-Hausdorff patterns (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/MultiplicityBridge.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weighted-approx-tangent-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-blowup-a1/parent-child-handoff.json`
- `/tmp/wat_scratch/ChildA.lean`
- `/tmp/wat_scratch/ChildB.lean`
- `/tmp/wat_scratch/ChildB2.lean`
- `/tmp/wat_scratch/Parent.lean`
- `/tmp/wat_scratch/Final.lean`
- `/tmp/wat_scratch/nc/frt_wat_integral_eq_setIntegral_mul/NodeChallenge.lean`
- `/tmp/wat_scratch/nc/frt_wat_setIntegral_blowUpMap_image/NodeChallenge.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c, and its Contract.lean is byte-identical to the workspace Contract and Submission. Mathlib has no varifold or blow-up integral lemma. SimonGMT has close analogues of the two children in Chapter04/WeightedBlowUp.lean (map_inverse_blowUp_carrier, integral_weighted_blowUp), Chapter04/TangentDensity.lean (hausdorff_blowUp_image) and Chapter04/MultiplicityBridge.lean (weight_eq_carrier_withDensity). They are stated for Chapter04's RectifiableVarifold and lie outside the Submission import closure, which also excludes ConstancyTangent's Grassmannian.eq_of_plane_eq. So the children reprove these facts from Mathlib facts that are in scope. Those facts are: Isometry.euclideanHausdorffMeasure_image (Volume/Measure.lean:131), Measure.euclideanHausdorffMeasure_smul₀ (:152), integral_withDensity_eq_integral_toReal_smul₀ (Bochner/ContinuousLinearMap.lean:311), setIntegral_eq_integral_of_forall_compl_eq_zero and setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (Bochner/Set.lean:486/442), MeasurableEmbedding.integral_map and integral_smul_measure (Bochner/Basic.lean:1093/1052), MeasurableEmbedding.restrict_map, Measure.restrict_restrict, restrict_smul and ae_restrict_mem₀ (Restrict.lean:890/205/193/637), withDensity_apply (WithDensity.lean:44), Homeomorph.measurableEmbedding, AEMeasurable.ennreal_ofReal and isometry_add_left. Inside the closure, the parent can use Grassmannian.ofSubmodule_plane (Varifold.lean:196) for S.plane = T.plane → S = T, Varifold.isOpen_domain (:336) and Grassmannian.finrank_plane (:126). Chapter03.blowUpMap unfolds by rfl from the non-module Submission. In scratch files importing GMT.Ch08.Submission in the comparator's replayed scope, both children are fully proved with axioms propext, Classical.choice and Quot.sound only. The frozen parent type is proved from them plus a sorry'd stub of the sibling frt_weight_blowup_tendsto, which is the only sorry. The verifier-generated NodeChallenge files elaborate, validate_lean_statement accepts both statements, and neither lean_name collides with the 77 DAG nodes.
