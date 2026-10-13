# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_completeness-a1`
- Child DAG node: `root.deformation-a1.im_completeness-a1.approx_tangent_locality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Lemma A (locality) of Step 5 of the parent proof, unweighted half; Step 6 of the parent proof uses exactly this half (chain "Lemma B, Lemma A (twice), Lemma B"). The Upper Density Theorem (Simon Ch. 1, 3.6 with Remark 3.7(2)) it invokes is the sibling zero_density (imc_ae_zero_density_off_set, the case W = ℝ^N of the comparator-accepted lpf_wtc_ae_zero_density_off_set), and the dilation identity ∫_{η_{x,r}(S)} g dH = r^{−k}∫_S g∘η_{x,r} dH is the comparator-accepted sibling blowup_cov (lpf_wtc_blowup_setIntegral_image).

Notation. H := μHE[k]; η_{x,r} := blowUpMap x r, η_{x,r}(y) = r⁻¹(y − x); B̄_ρ(y) := closedBall y ρ. For a set S, f ∈ C_c(ℝ^N) and r > 0 put I_S(r) := ∫_{η_{x,r}(S)} f dH. HasApproximateTangentSpaceAt k S x Q means: finrank Q = k and I_S(r) → ∫_Q f dH as r → 0+ for every f ∈ C_c(ℝ^N).

1. (Density zero of E′ ∖ E at points of E.) S := E′ ∖ E is H-null-measurable, and for every compact K, ∫⁻_{S∩K} 1 dH = H(S ∩ K) ≤ H(E′ ∩ K) < ∞. The sibling zero_density (imc_ae_zero_density_off_set), applied with Q := N, n := k, S := E′ ∖ E and g := 1, gives: for H-a.e. y with y ∉ E′ ∖ E, H((E′ ∖ E) ∩ B̄_ρ(y)) / ENNReal.ofReal(ρ^k) → 0 as ρ → 0+. Every y ∈ E satisfies y ∉ E′ ∖ E, so this holds for H-a.e. y ∈ E; an H-a.e. property restricted to E holds H⌞E-a.e. Let x ∈ E be such a point; the exceptional set does not depend on Q or f.

2. (Change of variables.) Fix such an x, a subspace Q and f ∈ C_c(ℝ^N); choose R > 0 with tsupport f ⊆ B̄_R(0) and let ‖f‖_∞ := sup |f|. For r > 0 put η := η_{x,r}. By blowup_cov (with Q := N, n := k, y := x, S := E, resp. S := E′, g := f), I_E(r) = r^{−k}∫_E f(η(z)) dH(z) and I_{E′}(r) = r^{−k}∫_{E′} f(η(z)) dH(z).

3. (Comparison.) The function z ↦ f(η(z)) is continuous, bounded by ‖f‖_∞ and vanishes unless ‖z − x‖ ≤ Rr, i.e. off the compact ball B̄_{Rr}(x). Since H(E′ ∩ B̄_{Rr}(x)) < ∞, f∘η is H-integrable on E′, on E and on E′ ∖ E. As E′ is the disjoint union of the H-null-measurable sets E and E′ ∖ E, ∫_{E′} f∘η dH = ∫_E f∘η dH + ∫_{E′∖E} f∘η dH. Therefore
 |I_{E′}(r) − I_E(r)| = r^{−k}|∫_{E′∖E} f∘η dH| ≤ ‖f‖_∞ r^{−k} H((E′ ∖ E) ∩ B̄_{Rr}(x)) = ‖f‖_∞ R^k · H((E′ ∖ E) ∩ B̄_{Rr}(x)) / (Rr)^k,
 which tends to 0 as r → 0+ by Step 1 (with ρ = Rr → 0+; all quantities are finite by local finiteness). Hence I_{E′}(r) − I_E(r) → 0 as r → 0+.

4. (Conclusion.) For x as in Step 1 and every subspace Q, the dimension conditions finrank Q = k of the two predicates coincide, and for every f ∈ C_c(ℝ^N), I_E(r) → ∫_Q f dH if and only if I_{E′}(r) → ∫_Q f dH, by Step 3. Hence HasApproximateTangentSpaceAt k E x Q ↔ HasApproximateTangentSpaceAt k E′ x Q for H⌞E-a.e. x, simultaneously for all Q. ∎

## Key steps

1. Upper Density Theorem (zero_density with S = E′∖E, g = 1): H((E′∖E) ∩ B̄_ρ(x)) = o(ρ^k) for H-a.e. x ∈ E.
2. Change of variables (blowup_cov): ∫_{η_{x,r}(S)} f dH = r^{−k}∫_S f∘η_{x,r} dH for S = E, E′.
3. |I_{E′}(r) − I_E(r)| = r^{−k}|∫_{E′∖E} f∘η| ≤ ‖f‖_∞ R^k H((E′∖E) ∩ B̄_{Rr}(x))/(Rr)^k → 0.
4. The blow-up integrals of E and E′ have the same limits for every f, so the approximate tangent spaces coincide for all Q.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean <snapshot>/project/GMT/Ch06/Contract.lean; cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp <snapshot>/project/GMT/Ch06/Contract.lean <snapshot>/project/GMT/Ch06/Submission.lean (all byte-identical)`
- `grep '^import' <snapshot>/project/GMT/Ch06/Contract.lean (8 imports) and a transitive SimonGMT import-closure walk (13 modules; Chapter01.Lusin not included)`
- `rg -n 'theorem MemLp.exists_hasCompactSupport_eLpNorm_sub_le|exists_hasCompactSupport_integral_sub_le' <snapshot>/mathlib/Mathlib (ContinuousMapDense.lean:141, :226); rg -n 'theorem ContinuousMap.exists_extension' <snapshot>/mathlib/Mathlib (TietzeExtension.lean:77): both files are outside the frozen closure`
- `rg -n 'theorem cauchySeq_of_edist_le_of_tsum_ne_top|theorem edist_le_tsum_of_edist_le_of_tendsto|theorem tendsto_integral_of_L1|theorem lintegral_tsum|theorem integral_indicator₀|theorem dist_convolution_le|theorem exists_continuous_zero_one_of_isClosed' <snapshot>/mathlib/Mathlib`
- `rg -n 'imc_' <snapshot>/project <snapshot>/mathlib and lake-packages-25730c7c/simongmt (no match); git log --all -S <each new imc_ name> (no commit); grep of the new names over runs/*/nodes (no match)`
- `python3 -I over dag.json: status, candidate commit, parent and lean_statement of the five reused names and of lpf_wtc_ae_zero_density_off_set; comparison of every new child type against all DAG node types (no duplicate); simulation of runtime.py _existing_lean_name_problem/_accepted_checkpoint and _topological on the current DAG (no problem; acyclic)`
- `sed -n 6532,6575p /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py (reuse rule), leaf_verification.py check_source_delta (no set_option in a leaf delta), decomposition_scope.py (recomputed parent_contract_digest 94deade2…)`
- `git show 12d217bba2a4:GMT/Ch06/Submission.lean (accepted zero-density proof) and git show 83e1f61809c1:GMT/Ch06/Submission.lean (accepted fiw_im_mass_formula: inline L¹ density and mollification)`
- `lake env lean /tmp/imc_v2/lean/Avail2.lean, Api3–Api7.lean (closure probes: Tietze, ContinuousMapDense, UniformContinuous.exists_contDiff_dist_le and Measurable.nat_floor absent; ContDiffBump, HasCompactSupport.contDiff_convolution_left and Lp.ae_tendsto_of_cauchy_eLpNorm present; NVector ContinuousAdd/PseudoMetrizableSpace workarounds)`
- `python3 -I /tmp/imc_v2/scripts/build_stmts.py (validate_lean_statement on all 13 types) and lake env lean /tmp/imc_v2/lean/Stmts.lean (all elaborate; only sorry warnings)`
- `lake env lean /tmp/imc_v2/lean/Test_deformation_im_completeness.lean, Test_imc_im_density_limit.lean, Test_imc_isRectifiableTriple_of_eventually_mem.lean, Test_imc_ae_tendsto_of_summable_lintegral.lean, Test_imc_ae_zero_density_off_set.lean (all compile at default heartbeats; standard axioms plus the stand-in sibling axioms)`
- `sed -n 560,735p book/sources/chapter-01-source.txt (Simon Ch. 1, 3.3–3.7 and the 5-times covering lemma)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-pairing-expansion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-lusi-5c440af24d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-frame-sign-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-blow-7c8d1035a6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-mass-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-01-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/decomposition_scope.py`
- `/tmp/imc_v2/lean/Stmts.lean`
- `/tmp/imc_v2/lean/Test_deformation_im_completeness.lean`
- `/tmp/imc_v2/lean/Test_imc_im_density_limit.lean`
- `/tmp/imc_v2/lean/Test_imc_isRectifiableTriple_of_eventually_mem.lean`
- `/tmp/imc_v2/lean/Test_imc_ae_tendsto_of_summable_lintegral.lean`
- `/tmp/imc_v2/lean/Test_imc_ae_zero_density_off_set.lean`

Pinned revisions confirmed: the frozen contract is byte-identical to the snapshot (Submission = Contract). The frozen import closure lacks Tietze (TietzeExtension.lean), L¹ density of C_c (ContinuousMapDense.lean) and SimonGMT Lusin. So mass_lower_bound's approximation step is proved inline from regularity, Urysohn and MemLp.induction_dense, as the accepted fiw_im_mass_formula does. Mathlib supplies the Riesz–Fischer and limit tools used by l1_cauchy_limit and density_limit (cauchySeq_of_edist_le_of_tsum_ne_top, edist_le_tsum_of_edist_le_of_tendsto, tendsto_integral_of_L1). Following the correction, the zero-density child uses the fresh name imc_ae_zero_density_off_set and is the W = ℝ^Q case of the accepted lpf_wtc_ae_zero_density_off_set; its Lean proof embeds that accepted proof (commit 12d217bb) and compiles. The five reused names are accepted checkpoints with identical types, and the controller's name check simulated on the current DAG passes. All 13 types validate and elaborate in the comparator scope. The parent compiles from mass_lower_bound, density_limit and tau_integrable; density_limit, limit_triple and l1_cauchy_limit also compile from their siblings; all at default heartbeats with axioms propext, Classical.choice and Quot.sound only. No imc_ name occurs in the project, SimonGMT, Mathlib, git history or the DAG.
