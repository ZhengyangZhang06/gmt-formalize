# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_plane_dist-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_plane_dist-a1.graph_plane_finrank-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof, with the linearity of graphPoint supplied by the sibling graph_point_linear_equiv.

Fix n, l, q and A. Write S := span_R{q(graphPoint v (A v)) : v in R^n} and E := EuclideanSpace.finAddEquivProd : R^(n+l) ≃L[R] R^n x R^l, Mathlib's canonical continuous linear equivalence.
1. (Representation.) By the sibling lemma rsod_graphPoint_eq_finAddEquivProd_symm, graphPoint x y = E.symm (x, y) for all x in R^n and y in R^l.
2. (A linear map.) Let Phi : R^n ->l[R] R^(n+l) be the composite of three R-linear maps: v |-> (v, A v) (LinearMap.prod of the identity and A), then E.symm : R^n x R^l -> R^(n+l), then q : R^(n+l) -> R^(n+l). So Phi is R-linear, and by step 1, Phi v = q(E.symm (v, A v)) = q(graphPoint v (A v)) for every v in R^n.
3. (S is the range of Phi.) By step 2 the generating set {q(graphPoint v (A v)) : v in R^n} equals Set.range Phi. This is the carrier of the submodule LinearMap.range Phi (LinearMap.coe_range). The span of the carrier of a submodule is that submodule (Submodule.span_eq), so S = LinearMap.range Phi.
4. (Phi is injective.) Suppose Phi v = Phi w. By step 2, q(E.symm (v, A v)) = q(E.symm (w, A w)). The linear isometry equivalence q is injective, and so is the equivalence E.symm. Hence (v, A v) = (w, A w) in R^n x R^l, and comparing first components gives v = w. This is the parent's observation that graphPoint v (A v) determines v, because its first n coordinates are v.
5. (Dimension count.) An injective linear map has range of the same finrank as its domain (LinearMap.finrank_range_of_inj). By steps 3 and 4, finrank S = finrank (LinearMap.range Phi) = finrank R^n. Since R^n = EuclideanSpace R (Fin n) has finrank n (finrank_euclideanSpace_fin), finrank S = n.

Remark (verified Lean realization; not part of the mathematical argument). The body below, placed after `theorem tdo_gpd_graph_plane_finrank : <frozen type> := by` inside `namespace Submission` of a module importing the frozen GMT.Ch05.Submission (contract opens in effect, Lean v4.35.0-rc3, Mathlib 25730c7c), compiled. The only other declaration in scope was a stub of the sibling rsod_graphPoint_eq_finAddEquivProd_symm. #print axioms gave [propext, Classical.choice, Quot.sound].
  intro n ℓ q A
  -- `Φ v = q (graphPoint v (A v))` as a linear map, via `graphPoint x y = E.symm (x, y)`
  set E : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ := EuclideanSpace.finAddEquivProd with hE
  let Φ : Rn n →ₗ[ℝ] Amb n ℓ :=
    q.toLinearEquiv.toLinearMap ∘ₗ (E.symm.toLinearEquiv.toLinearMap ∘ₗ
      (LinearMap.id.prod A.toLinearMap))
  have hΦ : ∀ v, Φ v = q (graphPoint v (A v)) := by
    intro v
    rw [rsod_graphPoint_eq_finAddEquivProd_symm]
    rfl
  have hrange : (Set.range fun v : Rn n => q (graphPoint v (A v))) =
      (LinearMap.range Φ : Set (Amb n ℓ)) := by
    rw [LinearMap.coe_range]
    ext z
    simp only [Set.mem_range, hΦ]
  have hinj : Function.Injective Φ := by
    intro v w hvw
    rw [hΦ, hΦ, rsod_graphPoint_eq_finAddEquivProd_symm,
      rsod_graphPoint_eq_finAddEquivProd_symm] at hvw
    have h := E.symm.injective (q.injective hvw)
    exact (Prod.mk.inj h).1
  rw [hrange, Submodule.span_eq, LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]

## Key steps

1. graphPoint x y = E.symm (x, y) by the sibling rsod_graphPoint_eq_finAddEquivProd_symm
2. Phi := q ∘ E.symm ∘ (id, A) is R-linear with Phi v = q(graphPoint v (A v))
3. S = span(range Phi) = LinearMap.range Phi (LinearMap.coe_range, Submodule.span_eq)
4. Phi is injective: q and E.symm are injective and (v, A v) determines v
5. finrank S = finrank R^n = n (LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin)

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
