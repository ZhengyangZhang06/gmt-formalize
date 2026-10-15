# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.flat_cone_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.flat_cone_plane-a1.planar_globalize-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 2 and 5–8 of the supplied proof of the parent (Submission.codim1_hcp_flat_cone_is_plane). The supplied proof shows that each connected component M_c of M is open and closed in H_c ∖ {0}, which is connected because m ≥ 2, so M_c = H_c ∖ {0}, and that two different planes would meet away from 0 by a dimension count in A₀. Here a component M_c is replaced by U_H ∩ M, where U_H is the union of all open sets on which M agrees with H. This is the same clopen argument and the same dimension count, without local connectedness or connected components. (Remark, not used in the proof: in the parent's terms U_H ∩ M is the union of the components M_c with H_c = H, so step 3 below is the parent's steps 4–6 for that union and step 5 below is the parent's step 7.) Sibling used: punctured_connected (Submission.codim1_hcp_fcp_punctured_subspace_isConnected). "Subspace" means linear subspace of ℝ^P, and B_ε(y) is an open ball. Book anchor: Simon, Appendix B, Theorem B.2 (book/chapter-B.txt lines 37–39); the printed proof ends with '|A|² ≡ 0 on M' (line 282) and leaves the passage from |A| ≡ 0 to a hyperplane implicit; the parent's supplied proof makes that passage explicit, and this child carries out part of it.

1. Uniqueness of local planes. Claim: let y ∈ M, let H₁, H₂ be subspaces and O₁, O₂ open sets with y ∈ O₁ ∩ O₂, O₁ ∩ M = O₁ ∩ H₁ and O₂ ∩ M = O₂ ∩ H₂. Then H₁ = H₂. By symmetry it suffices to show H₁ ⊆ H₂. Since y ∈ O₁ ∩ M = O₁ ∩ H₁ and y ∈ O₂ ∩ M = O₂ ∩ H₂, y ∈ H₁ and y ∈ H₂. Let h ∈ H₁. O₁ ∩ O₂ is open and contains y, so B_ε(y) ⊆ O₁ ∩ O₂ for some ε > 0. Put s := ε/(2(|h| + 1)) > 0 and z := y + sh. Then |z − y| = s|h| < ε, so z ∈ O₁ ∩ O₂. Also z ∈ H₁, as y, h ∈ H₁. Hence z ∈ O₁ ∩ H₁ = O₁ ∩ M, so z ∈ M. Then z ∈ O₂ ∩ M = O₂ ∩ H₂, so z ∈ H₂. Therefore sh = z − y ∈ H₂ and h = s⁻¹(sh) ∈ H₂.

2. The maximal agreement set. For a subspace H let U_H be the union of all open sets O ⊆ ℝ^P with O ∩ M = O ∩ H. Then: (i) U_H is open; (ii) every open O with O ∩ M = O ∩ H satisfies O ⊆ U_H; (iii) U_H ∩ M = U_H ∩ H, since a point of U_H lies in some member O of the union, and O ∩ M = O ∩ H.

3. Claim: if dim H ≥ 2 and U_H ∩ M ≠ ∅, then H ∖ {0} ⊆ U_H. Let K := H ∖ {0}, which is connected by punctured_connected. Let G := ℝ^P ∖ closure(U_H ∩ M), an open set.
 (a) K ⊆ U_H ∪ G. Let z ∈ K. If z ∉ closure(U_H ∩ M), then z ∈ G. Otherwise z ∈ closure(U_H ∩ M) ⊆ closure(M) ⊆ M ∪ {0} and z ≠ 0, so z ∈ M. By hypothesis there are a subspace H_z and an open O_z with z ∈ O_z and O_z ∩ M = O_z ∩ H_z. O_z is an open neighbourhood of a point of closure(U_H ∩ M), so it contains some y ∈ U_H ∩ M. Apply step 1 at y ∈ M to the open sets U_H ∋ y (with U_H ∩ M = U_H ∩ H by 2(iii)) and O_z ∋ y (with O_z ∩ M = O_z ∩ H_z): H = H_z. So O_z ∩ M = O_z ∩ H, hence O_z ⊆ U_H by 2(ii), and z ∈ U_H.
 (b) K ∩ U_H ∩ G = ∅. If z ∈ K ∩ U_H, then z ∈ U_H ∩ H = U_H ∩ M ⊆ closure(U_H ∩ M) by 2(iii), so z ∉ G.
 (c) U_H and G are open, and K is preconnected. By (a) and (b), K ⊆ U_H or K ⊆ G (Mathlib: isPreconnected_iff_subset_of_disjoint). Pick y₀ ∈ U_H ∩ M. Then y₀ ∈ U_H ∩ H by 2(iii), and y₀ ≠ 0 because 0 ∉ M, so y₀ ∈ K. But y₀ ∈ U_H ∩ M ⊆ closure(U_H ∩ M), so y₀ ∉ G. Hence K ⊄ G, and therefore K ⊆ U_H.

4. The plane H₀. Since M ≠ ∅, pick x₀ ∈ M. By hypothesis there are a subspace H₀ ⊆ A₀ with dim H₀ = m and an open O₀ with x₀ ∈ O₀ and O₀ ∩ M = O₀ ∩ H₀. By 2(ii), O₀ ⊆ U_{H₀}, so x₀ ∈ U_{H₀} ∩ M. As dim H₀ = m ≥ 2, step 3 gives H₀ ∖ {0} ⊆ U_{H₀}. Consequently H₀ ∖ {0} ⊆ U_{H₀} ∩ H₀ = U_{H₀} ∩ M ⊆ M, using 2(iii).

5. M ⊆ H₀ ∖ {0}. Let y ∈ M. By hypothesis there are a subspace H_y ⊆ A₀ with dim H_y = m and an open O_y with y ∈ O_y and O_y ∩ M = O_y ∩ H_y. As in step 4, y ∈ U_{H_y} ∩ M and H_y ∖ {0} ⊆ U_{H_y}. Dimension count: H₀ + H_y ⊆ A₀, so dim(H₀ + H_y) ≤ dim A₀ = m + 1. The dimension formula gives dim(H₀ + H_y) + dim(H₀ ∩ H_y) = dim H₀ + dim H_y = 2m (Mathlib: Submodule.finrank_sup_add_finrank_inf_eq). Hence dim(H₀ ∩ H_y) ≥ 2m − (m + 1) = m − 1 ≥ 1. So H₀ ∩ H_y ≠ {0}, and there is w ∈ H₀ ∩ H_y with w ≠ 0. Then w ∈ H₀ ∖ {0} ⊆ U_{H₀} (step 4) and w ∈ H_y ∖ {0} ⊆ U_{H_y}. Also w ∈ U_{H₀} ∩ H₀ = U_{H₀} ∩ M, so w ∈ M. Step 1 at w, with the open sets U_{H₀} and U_{H_y} and the identities 2(iii), gives H₀ = H_y. Finally y ∈ O_y ∩ M = O_y ∩ H_y, so y ∈ H_y = H₀, and y ≠ 0 because 0 ∉ M. Thus y ∈ H₀ ∖ {0}.

6. Conclusion. By steps 4 and 5, M = H₀ ∖ {0}, and dim H₀ = m (Module.finrank ℝ H₀ = m). ∎

## Key steps

1. Two local plane pairs (H₁, O₁), (H₂, O₂) at the same point y ∈ M have H₁ = H₂ (move from y along h ∈ H₁ inside O₁ ∩ O₂).
2. U_H := ⋃{O open : O ∩ M = O ∩ H} is open with U_H ∩ M = U_H ∩ H, and contains every such O.
3. If dim H ≥ 2 and U_H ∩ M ≠ ∅, then U_H and the complement of closure(U_H ∩ M) separate the connected set H ∖ {0}; closure(M) ⊆ M ∪ {0} and uniqueness give the covering, so H ∖ {0} ⊆ U_H.
4. For H₀ from a point x₀ ∈ M, H₀ ∖ {0} ⊆ M. For any y ∈ M the planes H₀ and H_y share some w ≠ 0 (dimension count in A₀), so uniqueness at w gives H_y = H₀ and y ∈ H₀ ∖ {0}.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 200,457p GMT/Ch07/Contract.lean (IsEmbeddedSubmanifold, tangentSpace)`
- `python3 -I scans of dag.json: hypercone_plane-a1 subtree statuses; nodes with lean_name chart_tangentSpace_eq_range_fderiv | dsmc_chart_inverse_continuity | dsmc_chart_range_subset_tangentSpace | dor_lmb_ret_chart_localization | codim1_ac_sat_chart_localization; regex IsConnected|IsPreconnected|connectedComponent|IsLocallyConstant|IsOpenMap over all lean_statement fields`
- `grep -rn 'isConnected_compl_singleton_of_one_lt_rank|isPreconnected_iff_subset_of_disjoint|is_const_of_fderiv|map_nhds_eq_of_equiv|finrank_sup_add_finrank_inf_eq|exists_mem_ne_zero_of_ne_bot|ContDiffAt.hasStrictFDerivAt|sup_orthogonal|isPreconnected_of_forall|IsPreconnected.union|Convex.isPreconnected|isOpen_induced_iff|orthogonalProjectionOnto|finrank_span_singleton|finrank_add_finrank_orthogonal' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lean -DautoImplicit=false Avail.lean / Avail2.lean (#check of the above after import GMT.Ch07.Submission)`
- `git show d626082a69a0:GMT/Ch07/Submission.lean and git show 7d0e7d04f4a8:GMT/Ch07/Submission.lean: byte comparison of frozen types; compile with #print axioms`
- `grep codim1_hcp_fcp in dag.json, GMT/, simongmt Poincare/, local-references project; git for-each-ref (2645 objects) | xargs git grep -l codim1_hcp_fcp -- 'GMT/*.lean'`
- `lean -DautoImplicit=false /tmp/fcp-split/check/{TypesAll,Assembly}.lean and /tmp/fcp-split/proofs/{IFT,Punct,Global,Local,All}.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `runtime.py: _existing_lean_name_problem, _accepted_checkpoint, accepted-reuse skip in child dispatch; nodes/*/decomposition-v1.json that reuse chart_tangentSpace_eq_range_fderiv / dsmc_chart_inverse_continuity`
- `grep -n 'B.2 Theorem|is a hyperplane|as required' book/chapter-B.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-d0551d00fd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a-534d529818/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-5d24065c78/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Connected/Clopen.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Connected/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Connected.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convex/PathConnected.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order.lean`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-B.txt`
- `/tmp/fcp-split/check/TypesAll.lean`
- `/tmp/fcp-split/check/Assembly.lean`
- `/tmp/fcp-split/proofs/All.lean`

Pins match. The manifest records project b4d606db and Mathlib 25730c7c. The snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Mathlib. The snapshot has every tool the children need, inside the import closure of GMT.Ch07.Submission:
- HasStrictFDerivAt.map_nhds_eq_of_equiv (InverseFunctionTheorem/FDeriv.lean:141) and ContDiffAt.hasStrictFDerivAt (ContDiff/RCLike.lean:62);
- IsOpen.is_const_of_fderiv_eq_zero (MeanValue.lean:617);
- isPreconnected_iff_subset_of_disjoint (Connected/Clopen.lean:248), isPreconnected_of_forall and IsPreconnected.union (Connected/Basic.lean:84,120), Convex.isPreconnected (Convex/PathConnected.lean:93);
- Submodule.finrank_sup_add_finrank_inf_eq (FiniteDimensional/Lemmas.lean:53) and Submodule.sup_orthogonal_of_hasOrthogonalProjection (Projection/Submodule.lean:49);
- orthogonalProjectionOnto (Projection/Basic.lean:120) and isOpen_induced_iff (Topology/Order.lean:412).
The one exception is isConnected_compl_singleton_of_one_lt_rank (Normed/Module/Connected.lean:125), which is not imported (#check fails). So punctured_connected gets an elementary half-space proof.

DAG. Three accepted declarations are relevant: chart_tangentSpace_eq_range_fderiv (candidate d626082a), dor_lmb_ret_chart_localization (candidate 7d0e7d04) and dsmc_chart_inverse_continuity. The first two are reused. Their frozen types are byte-identical to the declarations in their candidate commits, and both print only propext, Classical.choice, Quot.sound. The runtime accepts cross-branch reuse of accepted nodes with identical type (_existing_lean_name_problem, _accepted_checkpoint). No existing node states local planarity, punctured connectivity, or open images of immersions. The 4 new codim1_hcp_fcp_ names are unused in dag.json, GMT/, SimonGMT, the snapshot and all 2645 git refs.

Lean.
- All 6 child types elaborate after import GMT.Ch07.Submission in the contract namespace and opens (TypesAll.lean, exit 0).
- The selected frozen type is kernel-checked from local_plane and planar_globalize (Assembly.lean). Its axioms are propext, Classical.choice, Quot.sound and those two children.
- Trial Lean proofs of all four new children and the parent compile (All.lean). Their only non-standard axioms are the two reused accepted lemmas.

Book. Simon App. B, Theorem B.2 is at chapter-B.txt:37–39. Its printed proof ends with |A|² ≡ 0 at line 282, leaving the step to a hyperplane implicit; this node supplies that step.
