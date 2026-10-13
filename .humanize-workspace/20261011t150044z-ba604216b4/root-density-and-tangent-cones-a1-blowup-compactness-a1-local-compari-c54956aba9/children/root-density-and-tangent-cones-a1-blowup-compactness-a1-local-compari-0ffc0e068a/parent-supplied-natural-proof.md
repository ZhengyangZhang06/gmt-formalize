# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_pieces-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_pieces-a1.chart_refinement-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 4–6 of the supplied proof of chart_pieces, for a single chart (ψ, V). That is the step of Simon's proof of Ch. 3, 2.4 (chapter-03.txt lines 375–378): 'decomposing Hⁿ-almost all M_j as a countable union if necessary and using the C¹ Approximation Theorem 1.5 of Ch. 2 … f|M_j = g_j|M_j, where g_j is C¹'.
- Sibling used: c1_approximation (Simon Ch. 2, Theorem 1.5; Lean codim1_rdo_c1_approximation).
- Change from the supplied step 4: it suffices that each compact piece lies in V, so the margin closedBall(q, 2ρ) ⊆ V_a is dropped. Tangent planes are handled on the whole chart ball by the sibling chart_tangent.

Facts used:
- H^N = μHE[N] equals Lebesgue measure L^N = volume on ℝ^N (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
- If φ is C-Lipschitz on a set A, then H^N(φ(Z)) ≤ C^N·H^N(Z) for every Z ⊆ A (SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn).

1. (Compact pieces of V.) There are compact sets K_m ⊆ V (m ∈ ℕ), possibly empty, with ⋃_m K_m = V.
- For instance, take the closed balls closedBall(q, ρ) ⊆ V with q ∈ ℚ^N and rational ρ > 0. They cover V: given y ∈ V, choose ε > 0 with ball(y, ε) ⊆ V, a rational ρ ∈ (0, ε/2) and q ∈ ℚ^N with |q − y| < ρ. Then y ∈ closedBall(q, ρ) ⊆ ball(y, 2ρ) ⊆ V.
- Enumerate these countably many balls; if there are none (V = ∅), put K_m := ∅.
- In Lean: SigmaCompactSpace.exists_compact_covering on the subtype V, which is locally compact by IsOpen.locallyCompactSpace; K_m is the image of the m-th set under the inclusion.

2. (ψ is Lipschitz on K_m.) A C¹ map is locally Lipschitz, hence Lipschitz on each compact set (ContDiff.locallyLipschitz, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact). So ψ is C_m-Lipschitz on K_m for some C_m ≥ 0, and u := f∘ψ is (L·C_m)-Lipschitz on K_m.

3. (McShane extension.) Let ū_m : ℝ^N → ℝ be (L·C_m)-Lipschitz with ū_m = f∘ψ on K_m (LipschitzOnWith.extend_real).

4. (C¹ approximation.) For k ∈ ℕ, apply c1_approximation to ū_m with ε := (k + 1)⁻¹ > 0. This gives a C¹ function g_{m,k} : ℝ^N → ℝ with
 L^N({ū_m ≠ g_{m,k}}) ≤ L^N({x : ū_m(x) ≠ g_{m,k}(x) or Dū_m(x) ≠ Dg_{m,k}(x)}) < (k + 1)⁻¹.
(The supplied proof uses ε = 2^{−k}; any positive sequence tending to 0 works.)

5. (Null sets.) Put Z_m := K_m ∩ ⋂_k {ū_m ≠ g_{m,k}}.
- For every k, Z_m ⊆ {ū_m ≠ g_{m,k}}, so L^N(Z_m) < (k + 1)⁻¹. Hence L^N(Z_m) = 0, and H^N(Z_m) = 0.
- Since Z_m ⊆ K_m and ψ is C_m-Lipschitz on K_m, H^N(ψ(Z_m)) ≤ C_m^N·H^N(Z_m) = 0.

6. (The pieces.) Enumerate ℕ × ℕ by b ∈ ℕ, writing (m, k) = Nat.unpair b. Put
 Y_b := K_m ∩ {y : ū_m(y) = g_{m,k}(y)} ∩ ψ⁻¹(M), F_b := g_{m,k}.
(a) F_b is C¹ (step 4).
(b) Y_b is Borel:
- K_m is compact, hence closed;
- {ū_m = g_{m,k}} is closed, since both functions are continuous;
- ψ⁻¹(M) is Borel, since ψ is continuous and M is Borel.
(c) Y_b ⊆ K_m and K_m is closed, so closure(Y_b) ⊆ K_m ⊆ V. Being a closed subset of the compact K_m, closure(Y_b) is compact.
(d) ψ(Y_b) ⊆ M, because Y_b ⊆ ψ⁻¹(M).
(e) Let y ∈ Y_b. Then y ∈ K_m, so f(ψ(y)) = ū_m(y) by step 3, and ū_m(y) = g_{m,k}(y) = F_b(y).

7. (Coverage.) Let x ∈ (M ∩ ψ(V)) ∖ ⋃_b ψ(Y_b). Write x = ψ(y) with y ∈ V, and choose m with y ∈ K_m (step 1).
- Suppose y ∉ Z_m. Then ū_m(y) = g_{m,k}(y) for some k. Since also ψ(y) = x ∈ M, y ∈ Y_b for b := Nat.pair m k. Then x ∈ ψ(Y_b), a contradiction.
- Hence y ∈ Z_m and x ∈ ψ(Z_m).
So (M ∩ ψ(V)) ∖ ⋃_b ψ(Y_b) ⊆ ⋃_m ψ(Z_m). By step 5 and countable subadditivity, its H^N-measure is 0. ∎

## Key steps

1. Cover the open V by countably many compact sets K_m ⊆ V.
2. ψ is Lipschitz on each K_m; extend f∘ψ restricted to K_m to a Lipschitz ū_m on ℝ^N (McShane).
3. c1_approximation gives C¹ g_{m,k} with L^N({ū_m ≠ g_{m,k}}) < 1/(k+1); Z_m := K_m ∩ ⋂_k{ū_m ≠ g_{m,k}} is null, and so is ψ(Z_m).
4. Pieces Y_{m,k} := K_m ∩ {ū_m = g_{m,k}} ∩ ψ⁻¹(M) are Borel with compact closure in V, map into M, and f∘ψ = g_{m,k} on them.
5. (M ∩ ψ(V)) ∖ ⋃ψ(Y_{m,k}) ⊆ ⋃_m ψ(Z_m) is H^N-null.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; cmp snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean (identical) and Contract.lean with Submission.lean (identical); git rev-parse HEAD = b4d606db (project_commit)`
- `rg -n 'theorem MeasurableSet.image_of_continuousOn_injOn|theorem LipschitzOnWith.extend_real|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|lemma LocallyLipschitzOn.exists_lipschitzOnWith_of_compact|theorem exists_measurable_superset_of_null|ContDiff.locallyLipschitz|SigmaCompactSpace.exists_compact_covering' in snapshot mathlib/Mathlib`
- `rg -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|abbrev Euclid|dtc_bc_lc_sl_cp_|codim1_rdo|doraggt' -g '*.lean' in snapshot project (only abbrev Euclid in Contract/Submission)`
- `grep -rn 'area_image_criticalSet_eq_zero|euclideanHausdorffMeasure_image_le_of_lipschitzOn' .lake/packages/simongmt/Poincare/SimonGMT; cat Chapter03/SubmanifoldCover.lean and Chapter03/DisjointCover.lean; sed -n 1,160p Chapter03/Rectifiable.lean; sed Chapter02/AreaCritical.lean 1-60 and 170-200; sed Chapter02/Lipschitz.lean 200-240`
- `lake env lean /tmp/cps_split/lean/Avail.lean (#check after import GMT.Ch07.Submission: AreaCritical and DisjointCover not in import closure; all cited Mathlib lemmas available)`
- `python3 -I scans of dag.json: records of c1_approx, c1_tangent, im_calculus, slicing-a1, chart_pieces-a1; cross-branch reused children (554, all accepted); statements with ContDiff ℝ 1 and InjOn/range, CountablyRectifiable and ContDiff, Pairwise image disjointness, HasApproximateTangentSpaceAt with LinearMap.range (fderiv`
- `python3 -I /tmp/cps_split/scripts/check_reuse.py: git show <candidate_commit>:GMT/Ch07/Submission.lean, exact declaration comparison and sorry scan for codim1_rdo_rectifiable_c1_cover 422aff28, codim1_rdo_c1pt_fderiv_lower_bound dd15d7b5, codim1_rdo_c1_piece_approxTangent 9ff76906, codim1_rdo_c1_approximation 38ed0bc3, doraggt_ae_approxTangent_transfer 422e346e, cmc_imRep_locality_restrict_sub 2af75d69, rsdic_ae_tangent_iff_of_subset a157a5f4, codim1_rdo_c1cov_image_ball_borel_finite 44d3b5c6`
- `python3 -I match of cluster-state/verification/verdicts/*.json by material.contract.id for the five reused nodes`
- `grep -c dtc_bc_lc_sl_cp_ dag.json; grep -rl dtc_bc_lc_sl_cp_ nodes/; git log --all -S 'dtc_bc_lc_sl_cp_' (no matches)`
- `grep -n '_existing_lean_name_problem|_solve_children|_install_parent_supplied_child_handoff|dependency_workspaces' /runtime/flows/gmt-claude-fa87c2bbbce7/_recursive_lean/runtime.py`
- `python3 -I /tmp/cps_split/scripts/gen_challenges.py (lean_contract.validate_lean_statement + gmt-compare.child_modules contract mode); lake env lean /tmp/cps_split/challenges/Challenge_<key>.lean for all 8 keys`
- `lake env lean /tmp/cps_split/lean/Assembly.lean, /tmp/cps_split/lean/ChildN1.lean, /tmp/cps_split/lean/ChildN2N3.lean with #print axioms`
- `git show 24f2011c:GMT/Ch07/Submission.lean; lake env lean /tmp/cps_split/combined/CPSCombined.lean (accepted candidate + 3 child proofs + parent assembly; #print axioms)`
- `sed -n 1,140p and 365,385p book/chapter-03.txt; read the accepted natural proofs of the five reused nodes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-c54956aba9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/verification/verdicts`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-fa87c2bbbce7/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/cps_split/lean/Avail.lean`
- `/tmp/cps_split/challenges`
- `/tmp/cps_split/lean/Assembly.lean`
- `/tmp/cps_split/lean/ChildN1.lean`
- `/tmp/cps_split/lean/ChildN2N3.lean`
- `/tmp/cps_split/combined/CPSCombined.lean`

Pins match: the snapshot manifest gives project b4d606db and mathlib 25730c7c, the snapshot Contract.lean equals the workspace Contract.lean, and Submission.lean is a byte copy.

SimonGMT: what is missing. It lacks Lemma 1.2 'only if'; SubmanifoldCover.lean proves only 'if'. It also lacks the C¹ approximation theorem, and DisjointCover's Remark 1.3 covers only sets, not parametrised pieces. AreaCritical and DisjointCover are not in the import closure of GMT.Ch07.Submission.

Mathlib (snapshot paths cited): it supplies every tool the new children need. These are Lusin–Souslin (MeasurableSet.image_of_continuousOn_injOn), McShane (LipschitzOnWith.extend_real), μHE[N] = volume on Euclid N, Lipschitz-on-compact for C¹ maps, σ-compact covers of open sets, and Borel null supersets.

DAG: five accepted declarations cover the supplied steps 1–3 and the sibling dependencies.
- codim1_rdo_rectifiable_c1_cover (422aff28) and codim1_rdo_c1pt_fderiv_lower_bound (dd15d7b5).
- codim1_rdo_c1_approximation (38ed0bc3), whose type is identical to c1_approx.
- codim1_rdo_c1_piece_approxTangent (9ff76906).
- doraggt_ae_approxTangent_transfer (422e346e).
Each is byte-identical to its DAG string, passed the comparator, has no sorry, and is reused as a child. Cross-branch reuse in the DAG always targets accepted nodes; the runtime links such reuse by Lean name and skips handoff installation.

Lean.
- The 3 new names are unreserved.
- All 8 types elaborate in contract-mode challenge modules.
- The parent's exact frozen type follows from the children.
- The 3 new children are proved from their dependencies' frozen types.
- In the accepted candidate 24f2011c, the complete chain compiles. Submission.dtc_bc_lc_sl_chart_pieces uses only propext, Classical.choice and Quot.sound.
