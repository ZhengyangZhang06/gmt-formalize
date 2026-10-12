# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- Child DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 5(i), i.e. Simon's printed proof of Thm 3.1.6 “⇒”: “since x ∈ N_j and N_j is a C¹ submanifold, lim ∫_{η_{x,r}(N_j)} f dHⁿ = ∫_{T_x N_j} f dHⁿ”. The proof uses the parent's method: a local injective C¹ parametrization of the submanifold near x, the area formula, and dominated convergence. The parametrization is the chart φ itself. The parent's graph map t ↦ x + t + w(t) is one particular injective C¹ parametrization of the same piece of the submanifold; using the chart directly removes the inverse-function-theorem step and leaves the area-formula and dominated-convergence argument unchanged.
Tools:
- The area formula simongmt Chapter02.integral_area_formula_of_injective_derivative (module Poincare.SimonGMT.Chapter02.WeightedArea). Let s ⊆ ℝᵐ be measurable and ψ : ℝᵐ → ℝ^N be injective on s and differentiable at every point of s with injective derivative. Then ∫_{ψ(s)} g dH^d = ∫_s J_ψ(u)·g(ψ(u)) dH^d(u) for every g : ℝ^N → ℝ, where d = finrank ℝ ℝᵐ = m (finrank_euclideanSpace_fin) and J_ψ(u) := Chapter02.areaJacobianAt ψ u = (fderiv ℝ ψ u).normDet ≥ 0.
- On ℝᵐ the measure Hᵐ := μHE[m] is Lebesgue measure (EuclideanSpace.euclideanHausdorffMeasure_eq_volume); in particular it is finite on compact sets.
- A ↦ A.normDet is continuous (simongmt Chapter02.continuous_normDet, module Poincare.SimonGMT.Chapter02.AreaApproximation).
Notation: Hᵐ := μHE[m] on ℝ^N and on ℝᵐ; η_{x,r}(y) := r⁻¹(y − x); B_ρ(p) is the closed ball and B̆_ρ(p) the open ball.
1. Chart and candidate plane. Fix x ∈ S. IsC1Submanifold m S at x gives open V ⊆ ℝᵐ, open W ⊆ ℝ^N with x ∈ W, and φ : ℝᵐ → ℝ^N that is C¹ on V and injective on V. Moreover φ(V) = W ∩ S, V ∩ φ⁻¹(K) is compact for every compact K ⊆ W, and Dφ(v) := fderiv ℝ φ v is injective for v ∈ V. As x ∈ W ∩ S = φ(V), pick v₀ ∈ V with φ(v₀) = x. Since V is open and φ is C¹ on V, φ is differentiable at every v ∈ V with derivative Dφ(v), and v ↦ Dφ(v) is continuous on V (ContDiffOn.continuousOn_fderiv_of_isOpen). Let L := Dφ(v₀), an injective linear map, and P := L(ℝᵐ) = LinearMap.range L. Since L is injective, finrank P = m (LinearMap.finrank_range_of_inj). Fix f ∈ C_c(ℝ^N, ℝ). It remains to show I(r) := ∫_{η_{x,r}(S)} f dHᵐ → ∫_P f dHᵐ as r ↓ 0.
2. Constants. Let M_f := sup|f| < ∞, and choose R > 0 with f(y) = 0 whenever ‖y‖ > R (tsupport f is compact). L is injective on the finite-dimensional space ℝᵐ, so it is antilipschitz (LinearMap.exists_antilipschitzWith): there is K > 0 with ‖u‖ ≤ K‖Lu‖. With c := 1/(2K) > 0, ‖Lu‖ ≥ 2c‖u‖ for all u. By continuity of Dφ at v₀ and openness of V, choose δ > 0 with B_δ(v₀) ⊆ V and ‖Dφ(v) − L‖ ≤ c for all v ∈ B_δ(v₀). Apply the mean value inequality on the convex set B_δ(v₀) (Convex.norm_image_sub_le_of_norm_fderiv_le) to v ↦ φ(v) − L(v − v₀), whose derivative Dφ(v) − L has norm ≤ c. It gives ‖φ(v₀ + w) − x − Lw‖ ≤ c‖w‖ for ‖w‖ ≤ δ, hence
(a) ‖φ(v₀ + w) − x‖ ≥ 2c‖w‖ − c‖w‖ = c‖w‖ whenever ‖w‖ ≤ δ.
J_φ(v) := Dφ(v).normDet ≥ 0 is continuous on V (Dφ is continuous on V and normDet is continuous). B_δ(v₀) ⊆ V is compact, so there is Λ ≥ 0 with J_φ(v) ≤ Λ for all v ∈ B_δ(v₀) (IsCompact.exists_bound_of_continuousOn).
3. Separation. Choose ε₀ > 0 with B_{ε₀}(x) ⊆ W. K₀ := B_{ε₀}(x) is compact, so V ∩ φ⁻¹(K₀) is compact, and Q := (V ∩ φ⁻¹(K₀)) ∖ B̆_δ(v₀) is compact (a closed subset of it). φ is continuous on Q. Also φ(v) ≠ x for v ∈ Q: otherwise φ(v) = φ(v₀), and injectivity on V gives v = v₀ ∈ B̆_δ(v₀). Hence ε₁ := min_{v ∈ Q} ‖φ(v) − x‖ > 0 if Q ≠ ∅. Let ε := min(ε₀, ε₁), or ε := ε₀ if Q = ∅. Then
(b) ‖φ(v) − x‖ ≥ ε for every v ∈ V with ‖v − v₀‖ ≥ δ.
Indeed, if φ(v) ∈ K₀ then v ∈ Q and ‖φ(v) − x‖ ≥ ε₁ ≥ ε; otherwise ‖φ(v) − x‖ > ε₀ ≥ ε.
4. Area formula. Fix r with 0 < r < ε/R. Put U_r := {u ∈ ℝᵐ : v₀ + ru ∈ V} (open, hence measurable) and ψ_r(u) := r⁻¹(φ(v₀ + ru) − x) = η_{x,r}(φ(v₀ + ru)). The map u ↦ v₀ + ru is a bijection of U_r onto V, so ψ_r(U_r) = η_{x,r}(φ(V)) = η_{x,r}(W ∩ S). Let B := B_R(0). Since f = 0 off B, f equals the indicator of B times f, so I(r) = ∫_{η_{x,r}(S) ∩ B} f dHᵐ (setIntegral_indicator, B closed). If y = η_{x,r}(z) ∈ B with z ∈ S, then ‖z − x‖ = r‖y‖ ≤ rR < ε ≤ ε₀, so z ∈ W. Hence η_{x,r}(S) ∩ B = η_{x,r}(W ∩ S) ∩ B = ψ_r(U_r) ∩ B, and by the same indicator argument I(r) = ∫_{ψ_r(U_r)} f dHᵐ.
ψ_r is injective on U_r, because φ is injective on V. By the chain rule, ψ_r is differentiable at each u ∈ U_r with Dψ_r(u) = r⁻¹·Dφ(v₀ + ru)·r = Dφ(v₀ + ru), which is injective; so J_{ψ_r}(u) = J_φ(v₀ + ru). The area formula with s := U_r gives
I(r) = ∫_{U_r} J_φ(v₀ + ru)·f(ψ_r(u)) dHᵐ(u) = ∫_{ℝᵐ} F_r dHᵐ, where F_r(u) := 1_{U_r}(u)·J_φ(v₀ + ru)·f(ψ_r(u)).
Concretely: on U_r the area-formula integrand areaJacobianAt ψ_r u · f(ψ_r u) equals J_φ(v₀ + ru)·f(ψ_r(u)) pointwise, so the set integrals over U_r agree (setIntegral_congr_fun, U_r measurable). Then integral_indicator turns ∫_{U_r} into ∫_{ℝᵐ} of the indicator.
Each F_r is a.e.-strongly measurable: it is the indicator of the open set U_r of a function that is continuous on U_r, because u ↦ v₀ + ru maps U_r into V, where φ and Dφ are continuous. Use ContinuousOn.aestronglyMeasurable on U_r and aestronglyMeasurable_indicator_iff. Do not try to prove measurability of u ↦ f(ψ_r(u)) on all of ℝᵐ: φ is arbitrary off V.
5. Domination. Let 0 < r < ε/R and F_r(u) ≠ 0. Then v := v₀ + ru ∈ V and f(ψ_r(u)) ≠ 0, so ‖ψ_r(u)‖ ≤ R, i.e. ‖φ(v) − x‖ ≤ rR < ε. By (b), ‖ru‖ < δ. By (a), c·r‖u‖ ≤ ‖φ(v) − x‖ ≤ rR, so ‖u‖ ≤ R/c. Also J_φ(v) ≤ Λ since v ∈ B_δ(v₀). Hence |F_r(u)| ≤ G(u) := Λ·M_f·1_{B_{R/c}(0)}(u) for every u and every r ∈ (0, ε/R). G is Hᵐ-integrable on ℝᵐ, being bounded and supported in a compact ball.
6. Pointwise limit. Fix u ∈ ℝᵐ and let r ↓ 0. Since v₀ + ru → v₀ ∈ V and V is open, u ∈ U_r for all small r > 0, so F_r(u) eventually equals J_φ(v₀ + ru)·f(ψ_r(u)) (pass to this function with Tendsto.congr'). J_φ(v₀ + ru) → J_φ(v₀) = J_L := L.normDet by continuity of Dφ at v₀ and of normDet. Also ψ_r(u) = r⁻¹(φ(v₀ + ru) − φ(v₀)) → Lu, since φ has Fréchet derivative L at v₀ and the difference quotient along the direction u converges. Use HasFDerivAt.lim with the scaling r⁻¹ → ∞, or the one-variable derivative of t ↦ φ(v₀ + tu) at 0 restricted to t > 0; the case u = 0 is trivial. Hence f(ψ_r(u)) → f(Lu) by continuity of f, and F_r(u) → J_L·f(Lu).
7. Conclusion. The filter r ↓ 0 (𝓝[>] 0) is countably generated. So dominated convergence (tendsto_integral_filter_of_dominated_convergence) with steps 4–6 gives I(r) = ∫ F_r dHᵐ → ∫_{ℝᵐ} J_L·f(Lu) dHᵐ(u). Apply the area formula to L itself with s := ℝᵐ: L is differentiable everywhere with derivative L, injective, and injective on ℝᵐ. It gives ∫_{ℝᵐ} J_L·f(Lu) dHᵐ(u) = ∫_{L(ℝᵐ)} f dHᵐ = ∫_P f dHᵐ. Since f ∈ C_c(ℝ^N, ℝ) was arbitrary and finrank P = m, P is the approximate tangent space: HasApproximateTangentSpaceAt m S x P.

## Key steps

1. chart (V, W, φ) at x and v₀ with φ(v₀) = x; L := Dφ(v₀) is injective, and P := L(ℝᵐ) has dimension m
2. lower bound ‖φ(v₀+w) − x‖ ≥ c‖w‖ on B_δ(v₀) by the mean value inequality, and a Jacobian bound Λ there
3. separation: ‖φ(v) − x‖ ≥ ε for v ∈ V outside B̆_δ(v₀), by compactness (properness) and injectivity
4. for r < ε/R, rewrite ∫_{η_{x,r}(S)} f as ∫_{U_r} J_φ(v₀+ru) f(ψ_r(u)) dHᵐ with ψ_r(u) = r⁻¹(φ(v₀+ru) − x), via the area formula
5. domination by Λ·sup|f|·1_{B_{R/c}(0)} and pointwise convergence to J_L f(Lu)
6. dominated convergence and the area formula for L give the limit ∫_P f dHᵐ

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
