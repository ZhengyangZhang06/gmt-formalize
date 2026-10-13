# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- Child DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_tangent_congr-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2 (change of the weight on an Hⁿ-null set) and 3 (locality: only A near x matters) of the parent proof, merged into one statement. The hypothesis that A is Hⁿ-null-measurable makes the a.e. comparison of the integrands legitimate for the restricted measures.
Notation: Hⁿ := μHE[n]; η := η_{x,r} (blowUpMap x r). For a fixed test function f, I_r := ∫_{η(A)} f(y)ϑ(x + ry) dHⁿ(y) and I'_r := ∫_{η(A')} f(y)ϑ'(x + ry) dHⁿ(y).
Sibling used: blowup_scaling (Submission.rsod_blowUpMap_measure_scaling), part (i).
1. Reduction. finrank P = n is part of the hypothesis. Fix f ∈ C_c(ℝ^{n+ℓ}, ℝ). Choose R > 0 with f = 0 off B_R(0): tsupport f is compact, hence contained in some closed ball about 0, whose radius may be enlarged to be ≥ 1. Choose ρ > 0 with B̆_ρ(x) ⊆ O (O is open and x ∈ O). We show I_r = I'_r for every r ∈ (0, ρ/R). The interval (0, ρ/R) belongs to the filter 𝓝[>] 0 (Ioo_mem_nhdsGT), and I_r → ϑ(x)∫_P f dHⁿ = ϑ'(x)∫_P f dHⁿ by hypothesis. So it then follows that I'_r → ϑ'(x)∫_P f dHⁿ (Tendsto.congr'), which is the claim because f was arbitrary.
2. Fix r ∈ (0, ρ/R) and put B := B_R(0) and B_x := B_{rR}(x) (closed balls). Then rR < ρ, so B_x ⊆ B̆_ρ(x) ⊆ O. Since ‖η(z)‖ = r⁻¹‖z − x‖, η(S) ∩ B = η(S ∩ B_x) for every set S. Also x + rη(z) = z for every z, and η is injective.
3. Cut-off. For any ψ : ℝ^{n+ℓ} → ℝ, the function y ↦ f(y)ψ(x + ry) vanishes off B, so it equals its indicator on the Borel set B. By setIntegral_indicator, for every set S, ∫_{η(S)} f(y)ψ(x + ry) dHⁿ(y) = ∫_{η(S) ∩ B} f(y)ψ(x + ry) dHⁿ(y) = ∫_{η(S ∩ B_x)} f(y)ψ(x + ry) dHⁿ(y). Hence I_r = ∫_s f(y)ϑ(x + ry) dHⁿ and I'_r = ∫_{s'} f(y)ϑ'(x + ry) dHⁿ, with s := η(A ∩ B_x) and s' := η(A' ∩ B_x).
4. η(Z) is null: by part (i) of blowup_scaling, ofReal(rⁿ)·Hⁿ(η(Z)) = Hⁿ(Z) = 0 and ofReal(rⁿ) ≠ 0, so Hⁿ(η(Z)) = 0.
5. s and s' agree up to η(Z). Let y ∈ s ∖ s' and write y = η(z) with z ∈ A ∩ B_x. If z ∉ Z, then z ∈ (A ∩ O) ∖ Z = (A' ∩ O) ∖ Z (because B_x ⊆ O), so z ∈ A' ∩ B_x and y ∈ s', a contradiction. Hence z ∈ Z and y ∈ η(Z). Symmetrically, using the hypothesis in the form (A' ∩ O) ∖ Z = (A ∩ O) ∖ Z, s' ∖ s ⊆ η(Z). By step 4, s and s' are Hⁿ-a.e. equal (ae_eq_set), so their set integrals coincide for every integrand (setIntegral_congr_set). Therefore I'_r = ∫_s f(y)ϑ'(x + ry) dHⁿ.
6. s is null-measurable. A ∩ B_x is null-measurable, so there is a Borel T ⊆ A ∩ B_x with Hⁿ((A ∩ B_x) ∖ T) = 0 (NullMeasurableSet.exists_measurable_subset_ae_eq). η is a measurable embedding ((Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ _)), so η(T) is Borel. Hⁿ(η((A ∩ B_x) ∖ T)) = 0 by part (i) of blowup_scaling, and s = η(T) ∪ η((A ∩ B_x) ∖ T). Hence s is null-measurable.
7. Integrands agree a.e. on s. For Hⁿ-a.e. y we have y ∉ η(Z) (step 4). For such y with y ∈ s, write y = η(z) with z ∈ A ∩ B_x. Then z ∉ Z, so z ∈ (A ∩ O) ∖ Z and ϑ(z) = ϑ'(z) by hypothesis. As x + ry = z, f(y)ϑ(x + ry) = f(y)ϑ'(x + ry). Since s is null-measurable, setIntegral_congr_ae₀ gives ∫_s f(y)ϑ(x + ry) dHⁿ = ∫_s f(y)ϑ'(x + ry) dHⁿ; no integrability is needed.
8. By steps 3, 5 and 7, I_r = ∫_s fϑ(x + r·) = ∫_s fϑ'(x + r·) = I'_r for every r ∈ (0, ρ/R). This completes the proof by step 1.

## Key steps

1. fix f supported in B_R(0) and ρ with B̆_ρ(x) ⊆ O; it suffices that the two blow-up integrals agree for 0 < r < ρ/R
2. cut both integrals to η(A ∩ B_{rR}(x)) and η(A' ∩ B_{rR}(x)), using f = 0 off B_R(0) and η(S) ∩ B_R(0) = η(S ∩ B_{rR}(x))
3. η(Z) is Hⁿ-null by blowup_scaling, and the two cut sets differ only inside η(Z), so their set integrals coincide
4. η(A ∩ B_{rR}(x)) is null-measurable, so a.e. point of it is η(z) with z ∈ (A ∩ O) ∖ Z, where the weights agree
5. the integrals coincide for small r, so the limits coincide (ϑ(x) = ϑ'(x))

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
