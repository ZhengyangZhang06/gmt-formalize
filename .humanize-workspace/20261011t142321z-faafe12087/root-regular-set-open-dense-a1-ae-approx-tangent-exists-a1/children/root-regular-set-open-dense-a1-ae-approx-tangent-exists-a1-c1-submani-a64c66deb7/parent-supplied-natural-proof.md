# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- Child DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 4 (“Each N_k is Borel: every y ∈ N_k has a chart (V, W, φ) with W ∩ N_k = φ(V), and φ(V) is closed in W because φ is continuous and proper into W; so N_k is locally closed, hence Borel”), with the details filled in. Fix m, N and S with IsC1Submanifold m S.
1. Charts. Fix y ∈ S. IsC1Submanifold m S gives open V ⊆ ℝᵐ and W ⊆ ℝ^N with y ∈ W, and φ : ℝᵐ → ℝ^N that is C¹ on V (in particular continuous on V). Moreover φ(V) = W ∩ S, and V ∩ φ⁻¹(K) is compact for every compact K ⊆ W.
2. Claim: W ∩ closure(S) ⊆ S. Let z ∈ W ∩ closure(S). As W is open, choose ε > 0 with B̆_ε(z) ⊆ W, and put K := B_{ε/2}(z) (closed ball). K is compact (ℝ^N is proper) and K ⊆ B̆_ε(z) ⊆ W. Hence Q := V ∩ φ⁻¹(K) is compact. φ is continuous on Q, so φ(Q) is compact and therefore closed. Also φ(Q) = φ(V) ∩ K = W ∩ S ∩ K (Set.image_inter_preimage).
3. z ∈ closure(W ∩ S ∩ K). Given δ > 0, since z ∈ closure(S) there is w ∈ S with ‖w − z‖ < min(δ, ε/2). Then w ∈ B̆_ε(z) ⊆ W and w ∈ K, so w ∈ W ∩ S ∩ K and ‖w − z‖ < δ. Since W ∩ S ∩ K = φ(Q) is closed, z ∈ φ(Q) ⊆ W ∩ S. In particular z ∈ S, which proves the claim of step 2.
4. For each y ∈ S, steps 1–3 give an open W_y with y ∈ W_y and W_y ∩ closure(S) ⊆ S. Let O := ⋃_{y ∈ S} W_y, an open set. Then S = O ∩ closure(S). If z ∈ S, then z ∈ W_z ⊆ O and z ∈ closure(S). Conversely, if z ∈ W_y ∩ closure(S) for some y ∈ S, then z ∈ S by the claim.
5. O is open and closure(S) is closed, so both are Borel. Hence S = O ∩ closure(S) is Borel (MeasurableSet).

## Key steps

1. take a chart (V, W, φ) at y ∈ S
2. for z ∈ W ∩ closure S pick a compact closed ball K ⊆ W about z; φ(V ∩ φ⁻¹K) = W ∩ S ∩ K is compact, hence closed
3. z lies in the closure of W ∩ S ∩ K, so z ∈ S; hence W ∩ closure S ⊆ S
4. S = (⋃_{y∈S} W_y) ∩ closure S
5. an open set intersected with a closed set is Borel

## Reference use

### local-project

Queries:
- `sha256(parent-child-handoff.json subproblem.natural_proof) == decomposition-scope-v{1,2,3}.json target.proof_sha256`
- `field-by-field sha256 diff of decomposition-v{1,2,3}.json subproblems (key, title, statement, lean_statement, lean_name, depends_on, natural_proof, proof_key_steps)`
- `grep -rlE 'rsod_blowUpMap_measure_scaling|rsod_ae_tendsto_density_zero_outside|rsod_isC1Submanifold_measurableSet|rsod_isC1Submanifold_approxTangent|rsod_ae_approxTangent_of_c1Cover|rsod_ae_weightedApproxTangent_of_unweighted|rsod_weightedApproxTangent_congr' <run dir> --exclude-dir=local-references (excluding this node's own dir); GMT; .lake/packages/simongmt; <snapshot>/project`
- `rg -l 'rsod_' <snapshot>/mathlib/Mathlib`
- `git grep -lE '<the 7 proposed names>' <tip> -- '*.lean' for each of the 128 distinct tips of 340 refs`
- `dag.json: occurrences of each proposed name, duplicate lean_name check, identical-type check, status of rsod_blowUp_setIntegral_eq / tae_c1_chart_image_approxTangent / aetp_c1_piece_approxTangent, sibling rectifiable_c1_cover-a1 lean_statement`
- `grep -n 'def IsC1Submanifold|structure RectifiableVarifold' GMT/Ch05/Submission.lean`
- `grep -n 'def blowUpMap|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'exists_isClosed_continuousOn|caratheodory' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `grep -n '1\.2 Lemma|1\.3 Remark|1\.6 Theorem|1\.7 Definition|1\.8 Remark|1\.9 Theorem' book/chapter-03.txt`
- `lake build GMT.Ch05.Submission (fresh scratch /tmp/aetangent-v4-kM1OXj)`
- `lake env lean AllChallenges.lean / Assembly.lean / Leaves.lean / LeafUD.lean / LibCheck.lean (run in parallel)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1/decomposition-scope-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/aetangent-v4-kM1OXj/AllChallenges.lean`
- `/tmp/aetangent-v4-kM1OXj/Assembly.lean`
- `/tmp/aetangent-v4-kM1OXj/Leaves.lean`
- `/tmp/aetangent-v4-kM1OXj/LeafUD.lean`
- `/tmp/aetangent-v4-kM1OXj/LibCheck.lean`
- `/tmp/aetangent-v4-scripts/gen.py`
- `/tmp/aetangent-v4-scripts/check_leaves.py`

Pins confirmed: project ea5607598f3133b40a13241f2e51517a8c6423cd (equal to workspace HEAD), Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json) and simongmt 2b3663083f3fe399b6296fb8eaee52169170e197 (lake-manifest.json). The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies.

This is a publication retry. The handoff proof sha256 a26c202b… equals proof_sha256 in decomposition-scope-v1/v2/v3.json. v2 and v3 are byte-identical in every subproblem field, all three audits are acceptable, and the DAG node has retry_operation = publication and no children.

Name scan, no match anywhere for any of the 7 proposed names:
- dag.json (200 nodes);
- other nodes' run files (145 decomposition files across 200 node dirs);
- GMT, simongmt and the snapshot project;
- snapshot Mathlib (rg 'rsod_': no files);
- Lean files at all 128 distinct git ref tips (340 refs).
No DAG node has a type identical to a proposed child. rsod_blowUp_setIntegral_eq is now accepted in the density_of_approx_tangent-a1 branch, but its type differs from all seven proposed types, so it is not reused.

Frozen definitions match the child proofs:
- IsC1Submanifold: charts V ⊆ Rn m, W open, ContDiffOn ℝ 1 φ V, InjOn, φ '' V = W ∩ S, properness, injective fderiv.
- blowUpMap x r y = r⁻¹ • (y - x).
- HasApproximateTangentSpaceAt and HasWeightedApproximateTangentSpaceAt: finrank P = n plus the 𝓝[>] 0 limit for every f : C_c(E, ℝ).
- The simongmt Lusin theorem (IsBorelRegularOuterMeasure.exists_isClosed_continuousOn) requires measurability for mu.caratheodory, which W's step 1 addresses.

Simon Ch. 3 printed text (book/chapter-03.txt): Remark 1.3, the proof of 1.6 '⇒', Remark 1.8(1) and Theorem 1.9 match children U and W and the parent glue. The printed bound written with M \ N_j is read as M \ M_j, matching the displayed decomposition; U uses C \ C_k.

Lean results (fresh build, v4.35.0-rc3, 3014 jobs):
- AllChallenges: 0 errors and 7 sorry warnings, so all 7 types elaborate in the exact comparator scope. The file is identical to attempt 3's up to target numbering.
- Assembly: 0 errors and exactly 8 sorry warnings (7 child stubs plus the sibling stub). The parent proof contains no sorry. All 7 `exact Submission.X` solution forms and the parent form typecheck.
- Leaves (S, B, G) and LeafUD (UD): complete proofs whose axioms are only propext, Classical.choice and Quot.sound.
- LibCheck: every library result cited by T, U, W, UD and the glue exists with the cited signature.

No Matrix/IsUnit construction occurs.
