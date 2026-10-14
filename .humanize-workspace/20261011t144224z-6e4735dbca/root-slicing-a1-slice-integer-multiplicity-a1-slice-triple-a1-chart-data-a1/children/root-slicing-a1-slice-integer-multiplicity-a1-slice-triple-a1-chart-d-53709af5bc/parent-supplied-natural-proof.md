# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.lipschitz_on_c1_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝⁿ = Eucl n = EuclideanSpace ℝ (Fin n) with Euclidean norm |·|. Lⁿ = volume (Lebesgue measure on ℝⁿ). Dh(w) := fderiv ℝ h w. "u is K-Lipschitz on Ω" means |u(y) − u(z)| ≤ K|y − z| for all y, z ∈ Ω.

Source. This is Step 2 of the proof of slicing_im_st_chart_data: the C¹ Approximation Theorem (Simon Ch. 2, Theorem 1.5) applied to a McShane extension. Here it is stated for an arbitrary real function that is Lipschitz on an open set. The C¹ Approximation Theorem is the sibling c1_approximation_real (Submission.lpf_c1_approximation_real). It states: if g : ℝⁿ → ℝ is K-Lipschitz and 0 < ε ≤ ∞, then there are a closed set A ⊆ ℝⁿ with Lⁿ(ℝⁿ ∖ A) < ε and a C¹ function h : ℝⁿ → ℝ such that, for every x ∈ A, g(x) = h(x) and g has Fréchet derivative Dh(x) at x.

Let Ω ⊆ ℝⁿ be open and let u : ℝⁿ → ℝ be K-Lipschitz on Ω.

1. (McShane extension.) There is g : ℝⁿ → ℝ that is K-Lipschitz on all of ℝⁿ with g = u on Ω. For example, take g(x) := inf_{y ∈ Ω} (u(y) + K|x − y|), or g := 0 if Ω = ∅ (Mathlib LipschitzOnWith.extend_real).

2. (C¹ approximation.) For k ∈ ℕ let ε_k := 1/(k + 1) ∈ (0, 1]. Apply the sibling c1_approximation_real to g, K and ε_k. This gives a closed set C_k ⊆ ℝⁿ with Lⁿ(ℝⁿ ∖ C_k) < 1/(k + 1) and a C¹ function h_k : ℝⁿ → ℝ such that, for every x ∈ C_k, g(x) = h_k(x) and g has Fréchet derivative Dh_k(x) at x.

3. (The sets.) Put A_k := Ω ∩ C_k. Then A_k ⊆ Ω.

4. (Values and derivatives on A_k.) Let w ∈ A_k.
   - u(w) = g(w) because w ∈ Ω (step 1), and g(w) = h_k(w) because w ∈ C_k (step 2). So u(w) = h_k(w).
   - Ω is open and contains w, so u = g on the neighbourhood Ω of w. If a function agrees near w with a function that has Fréchet derivative L at w, then it also has Fréchet derivative L at w (HasFDerivAt.congr_of_eventuallyEq).
   - g has Fréchet derivative Dh_k(w) at w (step 2). Hence u has Fréchet derivative Dh_k(w) = fderiv ℝ h_k w at w.

5. (Null remainder.) Fix k ∈ ℕ.
   - If w ∈ Ω ∖ ⋃_l A_l, then w ∉ C_k; otherwise w ∈ Ω ∩ C_k = A_k. So Ω ∖ ⋃_l A_l ⊆ ℝⁿ ∖ C_k.
   - Hence Lⁿ(Ω ∖ ⋃_l A_l) ≤ Lⁿ(ℝⁿ ∖ C_k) < 1/(k + 1).
   This holds for every k ∈ ℕ, and 1/(k + 1) → 0 as k → ∞ (ENNReal.tendsto_inv_nat_nhds_zero). Therefore Lⁿ(Ω ∖ ⋃_k A_k) = 0.

6. (Conclusion.) Steps 2–5 give the required C¹ functions h_k : ℝⁿ → ℝ and sets A_k ⊆ Ω (k ∈ ℕ):
   - for every k and every w ∈ A_k, u(w) = h_k(w) and u has Fréchet derivative fderiv ℝ h_k w at w;
   - Lⁿ(Ω ∖ ⋃_k A_k) = 0. ∎

## Key steps

1. McShane: extend u|Ω to a K-Lipschitz g : ℝⁿ → ℝ (LipschitzOnWith.extend_real).
2. Sibling c1_approximation_real with ε = 1/(k+1): closed C_k and C¹ h_k with Lⁿ(ℝⁿ ∖ C_k) < 1/(k+1), g = h_k and g has derivative Dh_k on C_k.
3. A_k := Ω ∩ C_k: there u = g = h_k, and since u = g on the open set Ω, u has derivative Dh_k(w) at every w ∈ A_k (HasFDerivAt.congr_of_eventuallyEq).
4. Ω ∖ ⋃_l A_l ⊆ ℝⁿ ∖ C_k for every k, so its Lⁿ-measure is < 1/(k+1) for all k, hence 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean and local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (all identical)`
- `python3 -I over dag.json: status, candidate_commit, lean_statement, children of lpf_lipschitz_c1_immersion_pieces, lpf_c1_approximation_real, lpf_ccr_hasDerivAt_line_of_comp, lpf_countably_rectifiable_c1_cover, slicing_im_coarea_chart_cover, slicing_im_tg_c1_chart_cover, slicing_im_coarea_pieces, slicing_im_st_weighted_tangent_on_c1_chart, lpf_weighted_tangent_on_c1_chart`
- `grep -c slicing_im_st_cd_ dag.json DAG.md dag.mmd issue-workers.json; grep -rl slicing_im_st_cd_ nodes/ (only this node's decomposition-v1.json); git log --all -S slicing_im_st_cd_ (no match)`
- `grep 'already reserved by active' cluster-state/logs/gmt-ch06/*.log; stat -c %w on those logs vs accepted-candidate.json mtimes of the reused nodes (7 cases)`
- `read /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, _reference_use_problem, decomposition loop) and store.py (update -> refresh); prompts.py DECOMPOSITION_AUDIT`
- `rg Mathlib snapshot: LipschitzOnWith.extend_real, MeasurableSet.image_of_continuousOn_injOn, ae_restrict_union_iff, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, lipschitzOnWith_of_nnnorm_fderiv_le, HasFDerivAt.congr_of_eventuallyEq, HasDerivAt.unique, comp_lipschitzOnWith, ENNReal.tendsto_inv_nat_nhds_zero, Denumerable.eqv`
- `grep SimonGMT: def CountablyRectifiable, areaRegularSet, area_image_compl_regularSet_eq_zero, area_image_criticalSet_eq_zero, area_image_nondifferentiable_eq_zero, euclideanHausdorffMeasure_image_le_of_lipschitzOn; import closure of Chapter02.AreaDomain (contains AreaLipschitz)`
- `sed book/sources/chapter-03-source.txt 1-90 (Simon Ch. 3, 1.1-1.3, printed proof of Lemma 1.2)`
- `read accepted parent-supplied-natural-proof.json of the three reused nodes; decomposition-v1.json of this node, of coarea-a1.pieces-a1, skeleton-polyhedral-a1 (v1, v2) and restriction-theory-a1 (v2, v3)`
- `python3 -I /tmp/cdv2-k9q4/scripts/build.py and gen_from_json.py (contract_scope from verifier/gmt-compare.py; lean_contract.validate_lean_statement; byte equality with dag.json records)`
- `lake env lean /tmp/cdv2-k9q4/src/Stmts2.lean, Final2.lean, Variant2.lean, NoImport.lean (all exit 0; only sorry warnings in Stmts2; axioms propext, Classical.choice, Quot.sound)`
- `independent reviewer subagent (/tmp/cdv2-review-7x3m): re-ran all Lean files, verdict ACCEPT-WITH-FIXES (wording fixes applied)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/Denumerable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-data-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-data-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-line-deriv-comp-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-pieces-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-skeleton-polyhedral-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-theory-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch06/bdbee2664a174f908f6a022a9b9c6907.log`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-03-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cdv2-k9q4/subproblems.json`
- `/tmp/cdv2-k9q4/src/Stmts2.lean`
- `/tmp/cdv2-k9q4/src/Final2.lean`
- `/tmp/cdv2-k9q4/src/Variant2.lean`
- `/tmp/cdv2-k9q4/src/NoImport.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract, byte-identical to the workspace Contract.lean and Submission.lean. Child types therefore use only contract, SimonGMT and Mathlib names, and all 5 elaborate in the exact comparator scope.
- Mathlib supplies:
  - LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308);
  - MeasurableSet.image_of_continuousOn_injOn (MeasureTheory/Constructions/Polish/Basic.lean:821);
  - ae_restrict_union_iff (MeasureTheory/Measure/Restrict.lean:568);
  - EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187);
  - Convex.lipschitzOnWith_of_nnnorm_fderiv_le (Analysis/Calculus/MeanValue.lean:507);
  - HasFDerivAt.congr_of_eventuallyEq (Analysis/Calculus/FDeriv/Congr.lean:176);
  - HasDerivAt.unique (Analysis/Calculus/Deriv/Basic.lean:396);
  - ENNReal.tendsto_inv_nat_nhds_zero (Topology/Instances/ENNReal/Lemmas.lean:486);
  - LipschitzWith.comp_lipschitzOnWith (Topology/EMetricSpace/Lipschitz.lean:231);
  - Denumerable.eqv (Basic/Denumerable.lean:71).
- SimonGMT supplies CountablyRectifiable (Chapter03/Rectifiable.lean:34), areaRegularSet and area_image_compl_regularSet_eq_zero (Chapter02/AreaLipschitz.lean:31 and :59), and euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean:216). AreaLipschitz is reachable from the AreaDomain import of accepted candidate f9637977.
- Neither library has the C¹ chart cover, C¹ approximation or the chart line derivative. These come from two sources:
  - the accepted lpf_lipschitz_c1_immersion_pieces, lpf_c1_approximation_real and lpf_ccr_hasDerivAt_line_of_comp, reused with byte-identical types (runtime.py _existing_lean_name_problem / _accepted_checkpoint permit this, since all three were accepted with a candidate_commit before this attempt began at 22:00:50Z);
  - two new kernel-checked children with fresh names.
- lpf_countably_rectifiable_c1_cover is not accepted, so its identical type is taken under a fresh name.
- The parent follows from the child types and the sibling weighted_tangent_chart with standard axioms only.
