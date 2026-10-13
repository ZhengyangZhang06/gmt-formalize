# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.flat_cone_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.flat_cone_plane-a1.local_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 1, 3 and 4 of the supplied proof of the parent (Submission.codim1_hcp_flat_cone_is_plane), carried out on one chart ball around the given point x: zero tangential derivative makes ν, and then z ↦ ν(x)·z, constant on the chart image (step 1 and the first half of step 3); the cone rays force the constant to be 0 (second half of step 3, used here only for t near 1); the inverse function theorem makes the chart image open in the plane (step 4). Siblings used: chart_tangent_space (Submission.chart_tangentSpace_eq_range_fderiv), chart_localization (Submission.dor_lmb_ret_chart_localization) and immersion_open (Submission.codim1_hcp_fcp_immersion_image_open_in_subspace). ⟨·,·⟩ is the Euclidean inner product, T_y := tangentSpace M y, B_ρ and B̄_ρ are open and closed balls. Book anchor: Simon, Appendix B, Theorem B.2 (book/chapter-B.txt lines 37–39); the printed proof ends with '|A|² ≡ 0 on M' (line 282) and leaves the passage from |A| ≡ 0 to a hyperplane implicit; the parent's supplied proof makes that passage explicit, and this child carries out part of it.

Fix x ∈ M.

1. Chart. Apply IsEmbeddedSubmanifold 1 m M at y = x: there are an open V ⊆ ℝ^m, an open W ⊆ ℝ^P with x ∈ W, and ψ : ℝ^m → ℝ^P with ψ of class C¹ on V, ψ injective on V, ψ(V) = W ∩ M, V ∩ ψ⁻¹(K) compact for every compact K ⊆ W, and Dψ(z) injective for every z ∈ V. Since x ∈ W ∩ M = ψ(V), choose v₀ ∈ V with ψ(v₀) = x. V is open, so choose δ > 0 with B := B_δ(v₀) ⊆ V. For v ∈ V: ψ(v) ∈ ψ(V) = W ∩ M, so ψ(v) ∈ M; ψ is differentiable at v (C¹ on the open set V); and chart_tangent_space (with N = M, d = m, r = 1 ≥ 1 and the chart data above) gives T_{ψ(v)} = range Dψ(v). In particular Dψ(v)a ∈ T_{ψ(v)} for every a ∈ ℝ^m.

2. ν ∘ ψ is constant on B. Let v ∈ B. ν is differentiable at ψ(v) ∈ M (hypothesis) and ψ is differentiable at v (step 1), so by the chain rule ν ∘ ψ is differentiable at v and D(ν ∘ ψ)(v)a = Dν(ψ(v))(Dψ(v)a) for a ∈ ℝ^m. Since ψ(v) ∈ M and Dψ(v)a ∈ T_{ψ(v)} (step 1), the flatness hypothesis gives Dν(ψ(v))(Dψ(v)a) = 0. So ν ∘ ψ is differentiable on B with zero derivative at every point of B. B is open and convex, hence preconnected, so ν ∘ ψ is constant on B (mean value theorem; Mathlib: IsOpen.is_const_of_fderiv_eq_zero). Since v₀ ∈ B and ψ(v₀) = x, ν(ψ(v)) = ν(x) =: n for every v ∈ B.

3. ψ(B) lies in an affine hyperplane. Let f(v) := ⟨n, ψ(v)⟩. For v ∈ B, f is differentiable at v with Df(v)a = ⟨n, Dψ(v)a⟩, by the chain rule for the continuous linear functional ⟨n, ·⟩. By step 2, n = ν(ψ(v)). By step 1, Dψ(v)a ∈ T_{ψ(v)}, and ψ(v) ∈ M. So the normality hypothesis at ψ(v) gives Df(v)a = ⟨ν(ψ(v)), Dψ(v)a⟩ = 0. As in step 2, f is constant on B: ⟨n, ψ(v)⟩ = ⟨n, ψ(v₀)⟩ = ⟨n, x⟩ for every v ∈ B.

4. Localization. Apply chart_localization with N = M, the open set W, the set V, the map ψ (continuous on V, being C¹ there), which is injective on V with ψ(V) = W ∩ M and has the compactness property of step 1, the point v₀ ∈ V and ε = δ > 0. It gives ρ > 0 with M ∩ B̄_ρ(ψ(v₀)) ⊆ ψ(V ∩ B_δ(v₀)). Since ψ(v₀) = x and B_δ(v₀) = B ⊆ V, this says M ∩ B̄_ρ(x) ⊆ ψ(B).

5. ⟨n, x⟩ = 0 (cone property). Put s := ρ/(|x| + 1) > 0 and t := 1 + s > 0. Then |tx − x| = |sx| = s|x| ≤ s(|x| + 1) = ρ, so tx ∈ B̄_ρ(x). Also tx ∈ M by the cone hypothesis (t > 0, x ∈ M). By step 4, tx = ψ(v) for some v ∈ B. Step 3 gives t⟨n, x⟩ = ⟨n, tx⟩ = ⟨n, ψ(v)⟩ = ⟨n, x⟩, that is, s⟨n, x⟩ = 0. As s ≠ 0, ⟨n, x⟩ = 0. With step 3: ⟨n, ψ(v)⟩ = 0 for every v ∈ B.

6. The plane H. n ∈ A₀ and |n| = 1 by the normality hypothesis at x, so n ≠ 0. Let H := A₀ ∩ (span{n})^⊥, a linear subspace with H ⊆ A₀. Dimension: span{n} ⊆ A₀ and span{n} + (span{n})^⊥ = ℝ^P (orthogonal decomposition; Mathlib: Submodule.sup_orthogonal_of_hasOrthogonalProjection), so A₀ + (span{n})^⊥ = ℝ^P has dimension P. dim span{n} = 1 and dim span{n} + dim (span{n})^⊥ = P, so dim (span{n})^⊥ = P − 1. The dimension formula dim(A₀ + (span{n})^⊥) + dim(A₀ ∩ (span{n})^⊥) = dim A₀ + dim (span{n})^⊥ (Mathlib: Submodule.finrank_sup_add_finrank_inf_eq) reads P + dim H = (m + 1) + (P − 1), so dim H = m. Moreover ψ(B) ⊆ H: for v ∈ B, ψ(v) ∈ M ⊆ A₀, and ⟨n, ψ(v)⟩ = 0 by step 5, i.e. ψ(v) ∈ (span{n})^⊥.

7. ψ(B) is open in H. Apply immersion_open to H (dim H = m, step 6), the open ball B, and ψ: ψ is C¹ on B because B ⊆ V; Dψ(v) is injective for v ∈ B ⊆ V; and ψ(B) ⊆ H by step 6. It gives an open O' ⊆ ℝ^P with O' ∩ H = ψ(B).

8. Conclusion. Let O := B_ρ(x) ∩ O', an open set. x ∈ O: x ∈ B_ρ(x) as ρ > 0, and x = ψ(v₀) ∈ ψ(B) = O' ∩ H ⊆ O'. O ∩ M ⊆ O ∩ H: if y ∈ O ∩ M, then y ∈ M ∩ B̄_ρ(x) ⊆ ψ(B) ⊆ H by steps 4 and 6. O ∩ H ⊆ O ∩ M: if y ∈ O ∩ H, then y ∈ O' ∩ H = ψ(B), so y = ψ(v) with v ∈ B ⊆ V, and y ∈ M by step 1. Hence O ∩ M = O ∩ H, where H ⊆ A₀ is a linear subspace with dim H = m, O is open and x ∈ O. Since x ∈ M was arbitrary, the statement is proved. ∎

## Key steps

1. Take a chart ψ with ψ(v₀) = x and a ball B = B_δ(v₀) ⊆ V; chart_tangent_space gives Dψ(v)a ∈ T_{ψ(v)}M.
2. Chain rule and flatness: D(ν∘ψ) = 0 on B, so ν∘ψ ≡ n := ν(x) (mean value theorem); then normality gives D⟨n, ψ⟩ = 0, so ⟨n, ψ(v)⟩ = ⟨n, x⟩ on B.
3. chart_localization gives ρ > 0 with M ∩ B̄_ρ(x) ⊆ ψ(B); the cone point (1 + s)x lies there, forcing ⟨n, x⟩ = 0.
4. H := A₀ ∩ n^⊥ has dimension m (dimension formula) and contains ψ(B); immersion_open gives an open O' with O' ∩ H = ψ(B).
5. O := B_ρ(x) ∩ O' satisfies x ∈ O and O ∩ M = O ∩ H.

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
