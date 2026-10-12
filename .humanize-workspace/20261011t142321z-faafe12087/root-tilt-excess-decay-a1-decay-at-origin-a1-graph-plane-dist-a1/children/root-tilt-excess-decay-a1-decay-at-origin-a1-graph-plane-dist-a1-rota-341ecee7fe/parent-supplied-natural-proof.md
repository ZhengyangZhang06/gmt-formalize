# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_plane_dist-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_plane_dist-a1.rotated_plane_dist-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5(a) of the parent proof, strengthened to an equality. The facts (G1)-(G3) and the projection identity that replaces (G4) come from the sibling graph_coordinates.

Fix n, l, q, a, b. Write P := rotatedPlane q = q(horizontalPlane n l), a submodule of R^(n+l) regarded as a set in infDist. Let pi := P.starProjection be the orthogonal projection onto P, which exists because P is finite dimensional. By the sibling lemma lip_approx_graph_coordinates applied to n, l, q, for all c, c' in R^n and d, d' in R^l:
(G1) graphPoint c d - graphPoint c' d' = graphPoint (c - c') (d - d');
(G2) ||graphPoint c d||^2 = ||c||^2 + ||d||^2;
(G3) every z in R^(n+l) equals graphPoint c d for some c, d;
(P) pi(q(graphPoint c d)) = q(graphPoint c 0).
1. (Norm consequences of (G2).) For all c, d: ||d|| <= ||graphPoint c d||, because ||graphPoint c d||^2 = ||c||^2 + ||d||^2 >= ||d||^2 and both norms are nonnegative. Also ||graphPoint 0 d|| = ||d||, because ||graphPoint 0 d||^2 = 0 + ||d||^2 and both norms are nonnegative.
2. (Points q(graphPoint c 0) lie in P.) For c in R^n, (P) with d = 0 gives q(graphPoint c 0) = pi(q(graphPoint c 0)). The projection pi takes values in P (Submodule.starProjection_apply_mem), so q(graphPoint c 0) lies in P.
3. (Every point of P has this form.) Let p in P. By (G3) applied to q^(-1)(p), there are c, d with q^(-1)(p) = graphPoint c d, so p = q(graphPoint c d). Since p lies in P, pi p = p (Submodule.starProjection_eq_self_iff). By (P), pi p = q(graphPoint c 0). Hence p = q(graphPoint c 0).
4. (Upper bound.) By step 2 with c = a, the point q(graphPoint a 0) lies in P, so infDist(q(graphPoint a b), P) <= dist(q(graphPoint a b), q(graphPoint a 0)) (infDist_le_dist_of_mem). This distance equals ||q(graphPoint a b) - q(graphPoint a 0)||, which is ||q(graphPoint a b - graphPoint a 0)|| since q is linear, and then ||graphPoint a b - graphPoint a 0|| since q is an isometry. By (G1) this is ||graphPoint (a - a) (b - 0)|| = ||graphPoint 0 b||, which is ||b|| by step 1. So infDist(q(graphPoint a b), P) <= ||b||.
5. (Lower bound.) P is nonempty since 0 lies in P. For a nonempty set s, r <= infDist(x, s) holds iff r <= dist(x, y) for all y in s (Metric.le_infDist). So let p in P. By step 3, p = q(graphPoint c 0) for some c. Then dist(q(graphPoint a b), p) = ||q(graphPoint a b - graphPoint c 0)|| = ||graphPoint a b - graphPoint c 0|| = ||graphPoint (a - c) (b - 0)|| = ||graphPoint (a - c) b||, using the linearity and isometry of q and (G1). By step 1 this is >= ||b||. Hence ||b|| <= infDist(q(graphPoint a b), P).
6. Steps 4 and 5 give infDist(q(graphPoint a b), rotatedPlane q) = ||b||.

Remark (verified Lean realization; not part of the mathematical argument). The body below, placed after `theorem tdo_gpd_infDist_rotatedPlane_graphPoint : <frozen type> := by` inside `namespace Submission` of a module importing the frozen GMT.Ch05.Submission (contract opens in effect, Lean v4.35.0-rc3, Mathlib 25730c7c), compiled. The only other declaration in scope was a stub of the sibling lip_approx_graph_coordinates. #print axioms gave [propext, Classical.choice, Quot.sound].
  intro n ℓ q a b
  obtain ⟨hsub, hnorm, hsurj, hproj⟩ := lip_approx_graph_coordinates n ℓ q
  -- `‖graphPoint 0 d‖ = ‖d‖` and `‖d‖ ≤ ‖graphPoint c d‖`
  have hge : ∀ (c : Rn n) (d : Rn ℓ), ‖d‖ ≤ ‖graphPoint c d‖ := by
    intro c d
    have h := hnorm c d
    have h0 : 0 ≤ ‖graphPoint c d‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖c‖, norm_nonneg d]
  have hzero : ∀ d : Rn ℓ, ‖graphPoint (0 : Rn n) d‖ = ‖d‖ := by
    intro d
    have h := hnorm 0 d
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  -- every point `q (graphPoint c 0)` lies in `T₀ = rotatedPlane q`
  have hmem : ∀ c : Rn n, q (graphPoint c 0) ∈ rotatedPlane q := by
    intro c
    rw [← hproj c 0]
    exact Submodule.starProjection_apply_mem _ _
  -- every point of `T₀` is of the form `q (graphPoint c 0)`
  have hform : ∀ p ∈ rotatedPlane q, ∃ c : Rn n, p = q (graphPoint c 0) := by
    intro p hp
    obtain ⟨c, d, hcd⟩ := hsurj (q.symm p)
    have hp' : p = q (graphPoint c d) := by
      rw [← hcd]
      simp
    refine ⟨c, ?_⟩
    have h := hproj c d
    rw [← hp', Submodule.starProjection_eq_self_iff.mpr hp] at h
    exact h
  apply le_antisymm
  · calc infDist (q (graphPoint a b)) (rotatedPlane q : Set (Amb n ℓ))
        ≤ dist (q (graphPoint a b)) (q (graphPoint a 0)) := infDist_le_dist_of_mem (hmem a)
      _ = ‖b‖ := by
        rw [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, hsub, sub_self, sub_zero,
          hzero]
  · rw [le_infDist ⟨0, (rotatedPlane q).zero_mem⟩]
    intro p hp
    obtain ⟨c, rfl⟩ := hform p hp
    rw [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, hsub, sub_zero]
    exact hge _ _

## Key steps

1. From (G2): ||d|| <= ||graphPoint c d|| and ||graphPoint 0 d|| = ||d||
2. q(graphPoint c 0) = pi(q(graphPoint c 0)) lies in P = rotatedPlane q
3. Every p in P equals q(graphPoint c 0): apply (G3) to q^(-1) p and use pi p = p together with (P)
4. Upper bound: infDist <= dist to q(graphPoint a 0) = ||graphPoint 0 b|| = ||b||
5. Lower bound via le_infDist: dist to q(graphPoint c 0) is ||graphPoint (a - c) b||, which is >= ||b||

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean`
- `grep -n 'graphPoint\|rotatedPlane\|horizontalPlane\|hsNorm\|abbrev Amb\|abbrev Rn\|^namespace\|^open' GMT/Ch05/Submission.lean; sed -n 1,80p GMT/Ch05/Submission.lean`
- `rg -n 'theorem (infDist_le_dist_of_mem|le_infDist|infDist_le_infDist_add_dist|infDist_eq_iInf|infDist_nonneg|infDist_zero_of_mem)\b' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean; rg -n 'lemma le_infDist' (same file)`
- `rg -n 'theorem finrank_range_of_inj|theorem LinearMap.finrank_range_of_inj' <snapshot>/mathlib/Mathlib; rg -n 'theorem span_eq' <snapshot>/mathlib/Mathlib/LinearAlgebra/Span/*.lean`
- `rg -n 'finrank_euclideanSpace_fin|finAddEquivProd' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n 'starProjection_apply_mem|starProjection_eq_self_iff|eq_starProjection_of_mem_of_inner_eq_zero' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/*.lean`
- `python3 -I scans of <run>/dag.json: lean_statements containing graphPoint; accepted nodes mentioning finrank/graphPoint/hsNorm/infDist; regex for HS operator bounds and finrank of graph spans; status and candidate_commit of the reused nodes; cross-parent reuse precedents`
- `rg -l -e 'tdo_gpd_' <run>/dag.json <run>/nodes <snapshot>/project <snapshot>/mathlib/Mathlib GMT .lake/packages/simongmt/Poincare; git log --all --oneline -S 'tdo_gpd_' (no match)`
- `git show e2915745:GMT/Ch05/Submission.lean; git show 18a457c4:GMT/Ch05/Submission.lean; git show 7372f81c:GMT/Ch05/Submission.lean (accepted proofs of the reused declarations)`
- `lake env lean -o /tmp/gpd-decomp/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; LEAN_PATH=...:/tmp/gpd-decomp/olean lean checks/{Types,Assembly,Full,Comparator,DepFinrank,DepInfDist}.lean`
- `python3 -I: lean_contract.validate_lean_statement on all six frozen types; grep of runtime.py for _existing_lean_name_problem and _accepted_checkpoint (reuse rules)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Span/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-plane-dist-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-plane-dist-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-plane-dist-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-graph-coordinates-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-c1-submanifold-graph-ball-a1-graph-poi-152c2738dc/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1-hs-norm-bounds-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-campanato-from-tilt-a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/tmp/gpd-decomp/checks/Types.lean`
- `/tmp/gpd-decomp/checks/Assembly.lean`
- `/tmp/gpd-decomp/checks/Full.lean`
- `/tmp/gpd-decomp/checks/Comparator.lean`
- `/tmp/gpd-decomp/checks/DepFinrank.lean`
- `/tmp/gpd-decomp/checks/DepInfDist.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea560759 and Mathlib 25730c7c. Its Contract.lean has the same sha256 (c966f51e...) as the workspace Contract.lean and Submission.lean.

Mathlib lemmas used (paths under mathlib/Mathlib):
- Metric.infDist_le_dist_of_mem and Metric.le_infDist: Topology/MetricSpace/HausdorffDistance.lean:500, 508.
- LinearMap.finrank_range_of_inj: LinearAlgebra/Dimension/Finrank.lean:127.
- Submodule.span_eq: LinearAlgebra/Span/Defs.lean:91.
- finrank_euclideanSpace_fin: Analysis/InnerProductSpace/PiL2.lean:205.
- EuclideanSpace.finAddEquivProd: Analysis/InnerProductSpace/PiL2.lean:378.
- Submodule.starProjection_apply_mem, eq_starProjection_of_mem_of_inner_eq_zero and starProjection_eq_self_iff: Analysis/InnerProductSpace/Projection/Basic.lean:156, 180, 290.

Accepted DAG declarations reused with byte-identical frozen types:
- lip_approx_graph_coordinates (e2915745);
- rsod_graphPoint_eq_finAddEquivProd_symm (18a457c4);
- lgc_hsNormSq_bounds (7372f81c).
Their accepted proofs compile in the full chain.

Other DAG findings:
- The same infDist equality occurs only inside unaccepted nodes (any_radius_gr_linear_algebra_basics, arp_rotatedPlane_graphPoint_coords), so it cannot be reused.
- No DAG node states the finrank of span{q(graphPoint v (A v))} apart from this node.

No-match results:
- The new names tdo_gpd_graph_plane_finrank and tdo_gpd_infDist_rotatedPlane_graphPoint occur nowhere in the DAG, node directories, snapshot (project and Mathlib), workspace GMT, simongmt or git history.
- Mathlib has no graphPoint- or rotatedPlane-specific lemmas; those are project definitions.

Lean results:
- The whole chain (3 accepted proofs + 2 new proofs + parent assembly) compiles sorry-free.
- The axioms are exactly propext, Classical.choice and Quot.sound.
- Comparator-style target checks pass for all six declarations.

No web source was needed: the mathematics is elementary finite-dimensional linear algebra.
