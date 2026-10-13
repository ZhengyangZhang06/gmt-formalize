# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.tangent_plane_dilation-a1`
- Child DAG node: `root.allard_tangent_cones-a1.tangent_plane_dilation-a1.plane_eq_of_integral_eq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof ("T' = T"), i.e. the plane half of the printed "Θ^n(μ_C, λy) = Θ^n(μ_C, y) (by 5.3)" step in the proof of Simon 8.5.7. Correction: the parent cites SimonGMT Grassmannian.eq_of_plane_eq, but that lemma (Chapter08/ConstancyTangent.lean) is not reachable from import GMT.Ch08.Submission ("Unknown constant"). Steps 5–6 below replace it by an argument that uses only imported lemmas.

Notation. H := μHE[n], a measure on ℝ^N = Euclidean N. For a set P, H⌞P := H.restrict P, so ∫ y in P, g y ∂H is by definition ∫ g d(H⌞P). For S ∈ G(N,n) = Grassmannian N n, let p_S := S.projectionLinearMap. This is the linear map ℝ^N → ℝ^N whose matrix in the standard orthonormal basis is S.1, and S.plane = range p_S by definition.

1. Dimensions. By Grassmannian.finrank_plane, finrank ℝ T.plane = n and finrank ℝ T'.plane = n.

2. Regularity. By step 1 and SimonGMT Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule (for a subspace P with finrank P = n, H⌞P is regular), H⌞T.plane and H⌞T'.plane are regular measures on ℝ^N.

3. Riesz uniqueness. ℝ^N is a Hausdorff, locally compact space with its Borel σ-algebra. Let g ∈ C_c(ℝ^N, ℝ). The hypothesis, read right to left, gives ∫ g d(H⌞T'.plane) = ∫ g d(H⌞T.plane). By Mathlib MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported, two regular measures with equal integrals against every g ∈ C_c(ℝ^N, ℝ) are equal. Its regularity instances come from step 2. Hence H⌞T'.plane = H⌞T.plane.

4. Supports. By SimonGMT Chapter03.support_euclideanHausdorffMeasure_restrict_submodule, the support of H⌞P is exactly P whenever finrank P = n. With step 1 and step 3, as subsets of ℝ^N,
 T'.plane = support(H⌞T'.plane) = support(H⌞T.plane) = T.plane.
Submodules with equal underlying sets are equal (SetLike.ext'), so T'.plane = T.plane as submodules.

5. A Grassmannian point is its orthogonal projection. Let S ∈ G(N,n).
 - p_S ∘ p_S = p_S (Grassmannian.projectionLinearMap_comp_self).
 - p_S is symmetric (Grassmannian.projectionLinearMap_isSymmetric).
 So p_S is a symmetric projection. By Mathlib LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range, it equals the orthogonal projection onto its range: p_S = (range p_S).starProjection = S.plane.starProjection, as linear maps. Also, by Grassmannian.toMatrix_projectionLinearMap, LinearMap.toMatrix b b p_S = S.1, where b is the standard orthonormal basis (Grassmannian.coordinateBasis).

6. Conclusion. Apply step 5 to S = T' and S = T, and use step 4:
 T'.1 = toMatrix(p_{T'}) = toMatrix(T'.plane.starProjection) = toMatrix(T.plane.starProjection) = toMatrix(p_T) = T.1.
G(N,n) is a subtype of N×N real matrices, so T' = T (Subtype.ext). ∎

## Key steps

1. finrank T.plane = finrank T'.plane = n, so H^n⌞T.plane and H^n⌞T'.plane are regular (SimonGMT regular_euclideanHausdorffMeasure_restrict_submodule).
2. Equal C_c integrals of two regular measures force H^n⌞T'.plane = H^n⌞T.plane (Measure.ext_of_integral_eq_on_compactlySupported).
3. The support of H^n⌞P is P (support_euclideanHausdorffMeasure_restrict_submodule), so T'.plane = T.plane.
4. Each p_S is a symmetric idempotent, hence p_S = S.plane.starProjection (isSymmetricProjection_iff_eq_coe_starProjection_range). Its coordinate matrix is S.1 (toMatrix_projectionLinearMap), so T'.1 = T.1 and T' = T.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `python3 dump of dag.json node ids, statuses, lean_names, lean_statements (frt_weight_blowup_tendsto accepted with candidate b951e87; frt_tangent_plane_unique and allard_tc_tangent_plane_density speculative drafts; 127 nodes, no duplicated lean_name)`
- `git show b951e87 -- GMT/Ch08/Submission.lean (accepted proof of Submission.frt_weight_blowup_tendsto); git show f0c2966 (s = 1 draft frt_tangent_plane_unique)`
- `rg -n "theorem smul_closedBall'|mul_div_mul_left|theorem integral_smul_measure|theorem integral_map |tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within|theorem ofReal_eq_ofReal_iff" mathlib/Mathlib`
- `rg -n "ext_of_integral_eq_on_compactlySupported|isSymmetricProjection_iff_eq_coe_starProjection_range|mem_smul_set_iff_inv_smul_mem₀|theorem map_apply " mathlib/Mathlib`
- `grep -rn "theorem regular_euclideanHausdorffMeasure_restrict_submodule|theorem support_euclideanHausdorffMeasure_restrict_submodule|theorem eq_of_plane_eq|toMatrix_projectionLinearMap|theorem finrank_plane|projectionLinearMap_eq_starProjection" Poincare/SimonGMT (pinned simongmt 2b3663083f3fe399b6296fb8eaee52169170e197)`
- `lake env lean Probe2.lean: #check @Grassmannian.eq_of_plane_eq / @Grassmannian.projectionLinearMap_eq_starProjection after import GMT.Ch08.Submission (both: Unknown constant)`
- `rg -n allard_tc_tpd over the snapshot project/, workspace GMT/ and dag.json (no match)`
- `sed -n 525,580p book/chapter-08.txt (printed 5.3 and the proof of 5.7: Θ^n(μ_C, λy) = Θ^n(μ_C, y) by 5.3)`
- `verifier gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement on both child statements; lake env lean on the generated NodeChallenge files (autoImplicit false)`
- `lake env lean /tmp/tpd-decomp/scratch/Children.lean and /tmp/tpd-decomp/scratch/ParentMinimal.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-plane-dilation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-plane-dilation-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-blowup-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/GroupWithZero/Action/Pointwise/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/tpd-decomp/scratch/Children.lean`
- `/tmp/tpd-decomp/scratch/ParentMinimal.lean`
- `/tmp/tpd-decomp/scratch/Probe2.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract and Submission. Mathlib has every non-varifold lemma the two children need: Measure.ext_of_integral_eq_on_compactlySupported (RieszMarkovKakutani/Real.lean:412) and LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range (InnerProductSpace/Projection/Basic.lean:672). The parent's inline steps need smul_closedBall', ENNReal.mul_div_mul_left, integral_map, integral_smul_measure, mem_smul_set_iff_inv_smul_mem₀ and ENNReal.ofReal_eq_ofReal_iff, which are also present. The pinned SimonGMT supplies Chapter03.regular_/support_euclideanHausdorffMeasure_restrict_submodule and Grassmannian.finrank_plane, toMatrix_projectionLinearMap, projectionLinearMap_comp_self and projectionLinearMap_isSymmetric, all reachable from GMT.Ch08.Submission. Grassmannian.eq_of_plane_eq (cited by the supplied step 5) and projectionLinearMap_eq_starProjection are NOT reachable (Unknown constant), so the plane child's proof avoids them. The only reusable accepted declaration is frt_weight_blowup_tendsto (accepted, b951e87), whose frozen type is exactly the supplied step 2; it is reused under the identical-type sharing rule. Both children and the parent assembly elaborate and check in the comparator scope with only propext, Classical.choice and Quot.sound, apart from the sorry-stubbed sibling allard_tc_tangent_plane_density.
