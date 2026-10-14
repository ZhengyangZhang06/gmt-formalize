# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.lipschitz_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Registration and depth note (context, not part of the numbered proof). Fresh name idtp_fons_cs_sos_lipschitz_approx_tangent. Its frozen type is byte-identical to that of dimred_cs_sos_lipschitz_approx_tangent (DAG node root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.lipschitz_tangent-a1, status decomposing), which is owned by the other parent root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1 (the node whose frozen type equals the selected node's) and is not comparator-accepted, so the runtime forbids reusing that name here. The numbered proof below is that node's independently audited parent-supplied proof, changed only as stated here. This node sits at depth 6, the configured maximum, so it is a machine leaf: its Lean proof adds only Submission.idtp_fons_cs_sos_lipschitz_approx_tangent, proves every auxiliary claim below inline (have/obtain/let/show), and adds no helper declaration and no import. The declarations of its listed dependencies are available because the controller merges their accepted candidates into this leaf's worktree before its implementation base is recorded. Changes: the proof is replaced. The original proof needed the SimonGMT area formula (an import that a leaf cannot add) to blow up one bi-Lipschitz piece. That blow-up is exactly the accepted dependency dpf_piece, so only the partition of the regular set into bi-Lipschitz pieces (step 1 of the original proof) remains.

Dependency used: dpf_piece, the accepted Submission.dpf_approxTangent_ae_bilipschitz_piece. For P, n ∈ ℕ, an open U ⊆ ℝ^P, a Borel Y ⊆ U with μHE[n](Y ∩ C) < ∞ for every compact C ⊆ U, an L-Lipschitz F : ℝ^n → ℝ^P, a Borel B ⊆ ℝ^n and m > 0 with m|a − a'| ≤ |F(a) − F(a')| for a, a' ∈ B, F differentiable with injective derivative at every point of B, and F(B) ⊆ Y, it gives: for (volume.restrict B)-a.e. b, HasApproximateTangentSpaceAt n Y (F b) (LinearMap.range (fderiv ℝ F b)).
Library facts (in scope after `import GMT.Ch07.Submission`, probed): Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (MeasureTheory/Function/Jacobian.lean), measurableSet_of_differentiableAt, measurable_fderiv, ContinuousLinearMap.isOpen_injective, LinearMap.injective_iff_antilipschitz, ZeroHomClass.bound_of_antilipschitz, ae_restrict_iff', ae_all_iff. The candidate of dpf_piece also brings `import Poincare.SimonGMT.Chapter02.AreaLipschitz`, which contains the optional shortcut measurableSet_areaRegularSet used in step 1.
Notation: DF(u) := fderiv ℝ F u; G := {u ∈ ℝ^k : F is differentiable at u, DF(u) is injective, F(u) ∈ Y}.
1. (G is Borel.) {u : F differentiable at u} is Borel (measurableSet_of_differentiableAt), and u ↦ DF(u) is Borel measurable (measurable_fderiv).
 The set 𝓘 of injective continuous linear maps ℝ^k → ℝ^P is open (Mathlib ContinuousLinearMap.isOpen_injective, since ℝ^k is finite-dimensional). Directly: if A ∈ 𝓘 and |Aw| ≥ c|w| with c > 0 (step 2), then every B with ‖B − A‖ < c satisfies |Bw| ≥ (c − ‖B − A‖)|w|, so B is injective.
 Hence {u : DF(u) ∈ 𝓘} is Borel. F⁻¹(Y) is Borel because F is continuous and Y is Borel. So G is Borel. (Equivalently, G = areaRegularSet F ∩ F⁻¹(Y), with SimonGMT measurableSet_areaRegularSet.)
2. (Tolerance function.) Let A ∈ 𝓘. An injective linear map out of the finite-dimensional ℝ^k is antilipschitz: LinearMap.injective_iff_antilipschitz gives K' > 0 with AntilipschitzWith K' A, and ZeroHomClass.bound_of_antilipschitz gives ‖w‖ ≤ K'‖Aw‖. Choose such K' and put c_A := 1/K' > 0, so |Aw| ≥ c_A|w| for all w. Put r(A) := c_A/2 ∈ ℝ≥0. For A ∉ 𝓘 put r(A) := 1. Then r(A) ≠ 0 for every A. (The hypothesis 0 < k of the statement is not needed anywhere in this proof.)
3. (Partition into approximately linear pieces.) For u ∈ G, F is differentiable at u, so HasFDerivWithinAt F (DF(u)) G u. Apply exists_partition_approximatesLinearOn_of_hasFDerivWithinAt with f := F, s := G, f' := fderiv ℝ F and the tolerance r. It gives sets t_i ⊆ ℝ^k (i ∈ ℕ) and continuous linear maps A_i such that:
 - each t_i is Borel and G ⊆ ⋃_i t_i;
 - ApproximatesLinearOn F A_i (G ∩ t_i) (r(A_i)), i.e. |F(a) − F(a') − A_i(a − a')| ≤ r(A_i)|a − a'| for all a, a' ∈ G ∩ t_i;
 - if G is nonempty, then for every i there is y_i ∈ G with A_i = DF(y_i).
 (The lemma also makes the t_i pairwise disjoint; this is not needed.)
4. (Bi-Lipschitz bound on a piece.) Fix i and put B_i := G ∩ t_i, a Borel set. Suppose B_i ≠ ∅. Then G ≠ ∅, so A_i = DF(y_i) with y_i ∈ G. Hence A_i ∈ 𝓘 and r(A_i) = c_{A_i}/2. Put m_i := c_{A_i}/2 > 0. For a, a' ∈ B_i,
 |F(a) − F(a')| ≥ |A_i(a − a')| − |F(a) − F(a') − A_i(a − a')| ≥ c_{A_i}|a − a'| − (c_{A_i}/2)|a − a'| = m_i|a − a'|.
5. (Tangent planes on a piece.) Still assume B_i ≠ ∅. Apply dpf_piece with n := k, U := univ (open), the given Y and F, B := B_i, Lipschitz constant K and m := m_i. Its hypotheses hold:
 - Y is Borel and Y ⊆ univ;
 - μHE[k](Y ∩ C) < ∞ for every compact C, by hypothesis (C ⊆ univ is automatic);
 - F is K-Lipschitz, B_i is Borel and m_i > 0;
 - the lower bound of step 4 holds on B_i;
 - every a ∈ B_i ⊆ G has F differentiable at a with DF(a) injective;
 - F(B_i) ⊆ Y, because B_i ⊆ F⁻¹(Y).
 Hence, for (volume.restrict B_i)-a.e. b, HasApproximateTangentSpaceAt k Y (F b) (LinearMap.range (fderiv ℝ F b)). Since B_i is Borel, ae_restrict_iff' turns this into: for volume-a.e. u, u ∈ B_i implies HasApproximateTangentSpaceAt k Y (F u) (LinearMap.range (fderiv ℝ F u)). If B_i = ∅, this last statement holds trivially.
6. (Conclusion.) By ae_all_iff (a countable intersection of full-measure sets has full measure), for volume-a.e. u the implication of step 5 holds for every i ∈ ℕ at once. Fix such a u and assume F(u) ∈ Y, F is differentiable at u and DF(u) is injective. Then u ∈ G ⊆ ⋃_i t_i, so u ∈ t_i for some i, and u ∈ B_i. Step 5 gives HasApproximateTangentSpaceAt k Y (F u) (LinearMap.range (fderiv ℝ F u : Euclid k →ₗ[ℝ] Euclid P)), which is the claim. ∎

## Key steps

1. G := {u : F differentiable at u, DF(u) injective, F(u) ∈ Y} is Borel; the tolerance is r(A) := c_A/2 for injective A (|Aw| ≥ c_A|w|) and 1 otherwise.
2. Mathlib's exists_partition_approximatesLinearOn_of_hasFDerivWithinAt covers G by countably many Borel pieces B_i = G ∩ t_i. On each, F is within r(A_i) of an injective A_i = DF(y_i), so |F(a) − F(a')| ≥ (c_{A_i}/2)|a − a'|.
3. The accepted dpf_piece (the blow-up of one bi-Lipschitz piece via the area formula) gives HasApproximateTangentSpaceAt k Y (F b) (range DF(b)) for a.e. b ∈ B_i.
4. ae_all_iff over i: a.e. u with F(u) ∈ Y and DF(u) injective lies in some B_i, which proves the claim.

## Reference use

### local-project

Queries:
- `python3 -I -c json.load(<snap>/manifest.json); git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `cmp GMT/Ch07/Contract.lean <snap>/project/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n '^def (IsMinimizingIn|IsConeCurrent|BoundaryVanishes|SameBoundary|blowUp|currentEval|approxTangentPlane)|^structure IMRep|^def IMRep\.(measure|Represents|action)' <snap>/project/GMT/Ch07/Contract.lean`
- `rg -n -i -l coarea <snap>/mathlib/Mathlib (no match)`
- `rg -n -i -l 'cartesian product of currents|slice of a current' <snap>/mathlib/Mathlib (no match)`
- `rg -n 'idtp_fons_cs_sos|dimred_cs_sos|dpf_approxTangent_ae_bilipschitz_piece|dimred_im_mass_measure' <snap>/project (no match)`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' <snap>/mathlib/Mathlib`
- `rg -n 'theorem measurableSet_of_differentiableAt|theorem measurable_fderiv' <snap>/mathlib/Mathlib`
- `rg -n "theorem ae_all_iff|theorem ae_restrict_iff'" <snap>/mathlib/Mathlib`
- `rg -n 'theorem isOpen_iUnion_countable' <snap>/mathlib/Mathlib/Topology/Bases.lean; rg -n 'theorem ContinuousLinearMap.isOpen_injective' <snap>/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean; rg -n 'theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero ' <snap>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n 'theorem weighted_area_formula_lipschitz_injOn|theorem area_image_compl_regularSet_eq_zero|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|def areaRegularSet|theorem measurableSet_areaRegularSet' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/{AreaLipschitz,Lipschitz}.lean`
- `python3 scans of dag.json: status, candidate_commit, lean_statement, parent of dimred_cs_split_off_spine, dimred_cs_sos_*, the 5 reuses and all accepted nodes; accepted candidates whose Submission.lean imports Poincare.SimonGMT.Chapter02.AreaLipschitz; absence of the 7 fresh names`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean for the 5 reuses (declaration with identical type present; a21680472b has import Poincare.SimonGMT.Chapter02.AreaLipschitz)`
- `cat cluster-state/verification/results/hoa43/20261013T160813Z-ch07-root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_densit-ej3048p6/{result.json,comparator-config.json}`
- `grep -n '_existing_lean_name_problem|_dependency_problem|_overlay_accepted_children|_leaf_author_task|max_depth' /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `lake env lean /tmp/idtp_sos_decomp/check/{Types,Names,NamesArea,Assembly,Assembly2,Assembly3}.lean`
- `python3 /tmp/idtp_sos_decomp/scripts/gates.py /tmp/idtp_sos_decomp/envelope_test3.json (ScopedDecomposition.model_validate; replay of Runtime._dependency_problem, _topological, _existing_lean_name_problem on dag.json)`
- `sed -n 395,420p book/chapter-07.txt (Simon Lemma 7.3.5)`
- `WebSearch: Simon Introduction to GMT Lemma 3.5 minimizing cone translation invariant S = [[R^m]] × S_0`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ac0f702949/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/idtp_sos_decomp/check/Assembly3.lean`
- `/tmp/idtp_sos_decomp/check/NamesArea.lean`
- `/tmp/idtp_sos_review/LipCheck.lean`
- `/tmp/idtp_sos_review/CarrierCheck.lean`
- `/tmp/idtp_sos_review/UsageCheck.lean`

Pins match: the snapshot manifest records project b4d606d (= workspace HEAD) and Mathlib 25730c7c (= workspace Mathlib); SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, which hold no Submission declarations; none of the 7 fresh names, nor the reused names, occur in the snapshot project. No coarea formula, slicing or Cartesian product of currents exists in the snapshot Mathlib (no match). Mathlib does have exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, measurableSet_of_differentiableAt, measurable_fderiv, ContinuousLinearMap.isOpen_injective, TopologicalSpace.isOpen_iUnion_countable and euclideanHausdorffMeasure_zero, all used by the child proofs. SimonGMT's area formula (weighted_area_formula_lipschitz_injOn, area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet) lies in Chapter02/AreaLipschitz.lean, outside the contract imports. In dag.json, the accepted dpf_approxTangent_ae_bilipschitz_piece (candidate a21680472b, comparator passed with propext, Quot.sound, Classical.choice) carries that import and proves the bi-Lipschitz-piece tangent lemma. The 5 reused declarations are accepted with byte-identical types present in their candidate commits. The six dimred_cs_sos_* children of the identical-type node dimred_cs_split_off_spine are unaccepted and owned by another parent, hence the fresh names. All 12 child types and the parent type elaborate. The parent assembly and the product_current usage checks compile; #print axioms shows only propext, Classical.choice and Quot.sound beyond the stubs' sorryAx. The runtime gate replay reports no problem.
