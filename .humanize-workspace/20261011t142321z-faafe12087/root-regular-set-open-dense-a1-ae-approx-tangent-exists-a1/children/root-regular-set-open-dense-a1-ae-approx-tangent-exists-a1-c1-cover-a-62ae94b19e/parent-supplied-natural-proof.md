# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- Child DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_cover_ae_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon's printed proof of Thm 3.1.6 “⇒” together with Remark 3.1.3, as copied in steps 4–5 of the parent proof. It is specialised to a Borel set C of finite measure that is covered, up to the null set Z, by the given C¹ submanifolds of finite measure.
Notation: Hⁿ := μHE[n]; η := η_{x,r} (blowUpMap x r); T_x A = P abbreviates HasApproximateTangentSpaceAt n A x P; B_ρ(p) is the closed ball; ν.real := (ν ·).toReal.
Siblings used:
- blowup_scaling (Submission.rsod_blowUpMap_measure_scaling).
- upper_density_zero (Submission.rsod_ae_tendsto_density_zero_outside): for every measure ν on ℝ^{n+ℓ} and every Borel S with ν(S) < ∞, for Hⁿ-a.e. x ∉ S, (ρⁿ)⁻¹·ν.real(S ∩ B_ρ(x)) → 0 as ρ ↓ 0.
- c1_submanifold_measurable (Submission.rsod_isC1Submanifold_measurableSet) and c1_submanifold_tangent (Submission.rsod_isC1Submanifold_approxTangent), both used with N := n + ℓ.
1. Measurability and Remark 1.3. Each N_k is Borel by c1_submanifold_measurable. For k ∈ ℕ put C_k := (C ∩ N_k) ∖ ⋃_{i<k} N_i. Each C_k is Borel and C_k ⊆ C ∩ N_k. If x ∈ C ∖ Z, then x ∈ ⋃_k N_k because C ⊆ Z ∪ ⋃_k N_k, and for the least k with x ∈ N_k we get x ∈ C_k. Hence C ∖ Z ⊆ ⋃_k C_k.
2. Exceptional sets. Fix k and put A¹_k := C ∖ C_k and A²_k := N_k ∖ C_k. Both are Borel, with Hⁿ(A¹_k) ≤ Hⁿ(C) < ∞ and Hⁿ(A²_k) ≤ Hⁿ(N_k) < ∞. Apply upper_density_zero with ν := Hⁿ to S := A¹_k and to S := A²_k. This gives an Hⁿ-null set E_k such that for every x ∉ E_k and each i ∈ {1, 2} with x ∉ Aⁱ_k, (ρⁿ)⁻¹·Hⁿ.real(Aⁱ_k ∩ B_ρ(x)) → 0 as ρ ↓ 0. Every x ∈ C_k lies outside both A¹_k and A²_k.
3. Scaling facts. Let r > 0. For every set A, Hⁿ(η(A)) = (rⁿ)⁻¹Hⁿ(A) by part (i) of blowup_scaling (ofReal(rⁿ)·Hⁿ(η(A)) = Hⁿ(A) with ofReal(rⁿ) ∈ (0, ∞)). For R > 0, η(A) ∩ B_R(0) = η(A ∩ B_{rR}(x)) because ‖η(z)‖ = r⁻¹‖z − x‖. η is injective, and η(A) is the preimage of A under the continuous map y ↦ x + ry, so η(A) is Borel whenever A is.
4. Splitting (printed proof of 1.6 “⇒”). Fix k and x ∈ C_k ∖ E_k. Since x ∈ C_k ⊆ N_k, N_k satisfies IsC1Submanifold n, and n ≥ 1, c1_submanifold_tangent gives a subspace P with T_x N_k = P; in particular finrank P = n. Fix f ∈ C_c(ℝ^{n+ℓ}, ℝ), let M_f := sup|f|, and choose R > 0 with f = 0 off B_R(0). Let r > 0. By step 3, η(C) and η(N_k) have finite Hⁿ-measure. f is continuous and bounded by M_f, so f is integrable on each of them and on their subsets (Measure.integrableOn_of_bounded). η(C_k), η(A¹_k) and η(A²_k) are Borel. Since η is injective, C_k ⊆ C and C_k ⊆ N_k, η(C) is the disjoint union of η(C_k) and η(A¹_k), and η(N_k) is the disjoint union of η(C_k) and η(A²_k). Additivity of the integral over disjoint sets with the second set measurable (setIntegral_union) gives
∫_{η(C)} f dHⁿ = ∫_{η(N_k)} f dHⁿ − ∫_{η(A²_k)} f dHⁿ + ∫_{η(A¹_k)} f dHⁿ.
5. Error terms. Let i ∈ {1, 2}. Since f = 0 off B_R(0), ∫_{η(Aⁱ_k)} f = ∫_{η(Aⁱ_k) ∩ B_R(0)} f (setIntegral_indicator), and η(Aⁱ_k) ∩ B_R(0) has finite measure. So norm_setIntegral_le_of_norm_le_const and step 3 give
|∫_{η(Aⁱ_k)} f dHⁿ| ≤ M_f·Hⁿ.real(η(Aⁱ_k) ∩ B_R(0)) = M_f·Hⁿ.real(η(Aⁱ_k ∩ B_{rR}(x))) = M_f·(rⁿ)⁻¹·Hⁿ.real(Aⁱ_k ∩ B_{rR}(x)) = M_f·Rⁿ·((rR)ⁿ)⁻¹·Hⁿ.real(Aⁱ_k ∩ B_{rR}(x)).
As r ↓ 0, ρ := rR ↓ 0 (r ↦ rR maps 𝓝[>] 0 to 𝓝[>] 0 because R > 0). So by step 2 (x ∈ C_k and x ∉ E_k) the right side tends to 0.
6. Main term and conclusion at x. ∫_{η(N_k)} f dHⁿ → ∫_P f dHⁿ because T_x N_k = P. By steps 4–5, ∫_{η(C)} f dHⁿ → ∫_P f dHⁿ as r ↓ 0. Since f was arbitrary and finrank P = n, T_x C = P. (This is Simon's Remark 1.5(2): T_x C = T_x N_k.)
7. Conclusion. Suppose x ∈ C has no approximate tangent space of C. Either x ∈ Z, or x ∈ C ∖ Z ⊆ ⋃_k C_k; in the latter case x ∈ C_k for some k, and then x ∈ E_k by step 6. Hence the exceptional set is contained in Z ∪ ⋃_k E_k, a countable union of Hⁿ-null sets. So for Hⁿ-a.e. x, x ∈ C implies that some P satisfies HasApproximateTangentSpaceAt n C x P.

## Key steps

1. each N_k is Borel (sibling); disjointify C_k := (C ∩ N_k) ∖ ⋃_{i<k} N_i, so that C ∖ Z ⊆ ⋃ C_k
2. the Upper Density Theorem (sibling upper_density_zero) for Hⁿ on C ∖ C_k and N_k ∖ C_k gives null sets E_k
3. at x ∈ C_k ∖ E_k: ∫_{η(C)} f = ∫_{η(N_k)} f − ∫_{η(N_k∖C_k)} f + ∫_{η(C∖C_k)} f
4. each error term is ≤ sup|f|·Rⁿ·((rR)ⁿ)⁻¹·Hⁿ(A ∩ B_{rR}(x)) → 0, via blowup_scaling and zero density
5. the main term → ∫_P f with P = T_x N_k, from the sibling c1_submanifold_tangent
6. the exceptional set lies in Z ∪ ⋃ E_k, which is null

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
