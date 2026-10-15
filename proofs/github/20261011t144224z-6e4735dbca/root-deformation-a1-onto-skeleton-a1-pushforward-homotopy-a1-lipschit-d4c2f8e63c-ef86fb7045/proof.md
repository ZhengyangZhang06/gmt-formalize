# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.boundary-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 7 of the supplied proof of lipschitz_pushforward, including fact (dP) (d commutes with pull-back for compatible forms), which is proved inline in step 5. Assume (RS) and (I), and fix m, m′, j, X ∈ D_{j+1}(ℝ^m), G, Λ, r, S with M(X) < ∞, M(∂X) < ∞, r > 0, G Λ-Lipschitz on (spt X)_r and proper on spt X, and LipPF(X, G, S).

1. (∂X satisfies the hypotheses of (I) with k := j.) By part (1) of the reused support_lemmas (U := univ), spt ∂X ⊆ spt X; supports of currents on univ are closed. M(∂X) < ∞ by assumption. HEq condition: let j′ ∈ ℕ and Y ∈ D_{j′+1}(ℝ^m) with j = j′ + 1 and HEq Y ∂X; substituting j = j′ + 1, HEq between terms of the same type gives Y = ∂X, so ∂Y = ∂∂X = 0 (GeometricCurrentOn.boundary_boundary), and M(0) = 0 < ∞, because the zero current takes the value 0 on every form, so every element of the supremum defining its mass is ENNReal.ofReal 0 = 0. Since (spt ∂X)_r ⊆ (spt X)_r (thickening is monotone in the set), G is Λ-Lipschitz on (spt ∂X)_r. G is proper on spt ∂X: for compact K, G⁻¹(K) ∩ spt ∂X = (G⁻¹(K) ∩ spt X) ∩ spt ∂X is the intersection of a compact set with a closed set.
2. (The push-forward of ∂X.) By (I) applied to ∂X (with k := j and the same G, Λ, r) there is S_∂ ∈ D_j(ℝ^{m′}) with LipPF(∂X, G, S_∂) (the first conjunct of (I)).
3. (Reference sequence and compatible forms.) Fix φ ∈ D^j(ℝ^{m′}). (RS) with F := spt X gives C^∞ maps G_n with ‖fderiv ℝ G_n x‖ ≤ Λ for all n and x ∈ O₀ := (spt X)_{r/2}, G_n → G uniformly on O₀, and G_n proper on spt X for all large n. O₀ is open and spt ∂X ⊆ spt X ⊆ O₀ (r/2 > 0), so (G_n) with O₀ and Λ is an admissible approximating sequence both in LipPF(X, G, ·) and in LipPF(∂X, G, ·). For each n such that G_n is proper on spt X, the reused compatible_form (P := m, Q := m′, U := V := univ, A := spt X, f := G_n, ω := φ) gives θ_n ∈ D^j(ℝ^m) and an open N_n ⊇ spt X with θ_n(x) = φ(G_n x).compContinuousLinearMap (DG_n(x)) for all x ∈ N_n; for the other n put θ_n := 0. So for all large n, θ_n is compatible with (G_n, φ) near spt X, hence also near spt ∂X (same N_n).
4. (Limit along ∂X.) LipPF(∂X, G, S_∂) applied to (G_n), O₀, Λ, φ and (θ_n) gives ∂X(θ_n) → S_∂(φ).
5. ((dP): d commutes with the pull-back.) Let n be as in step 3 and x ∈ N_n. Let p_n(x′) := φ(G_n x′).compContinuousLinearMap (DG_n(x′)). N_n is an open neighbourhood of x on which θ_n = p_n, so θ_n and p_n agree near x and their exterior derivatives at x agree (Filter.EventuallyEq.extDeriv_eq). Since φ is C^∞ (hence differentiable at G_n(x)) and G_n is C^∞ (hence ContDiffAt of order ≥ 2 at x), Mathlib's extDeriv_pullback gives (extDeriv p_n)(x) = (extDeriv φ)(G_n x).compContinuousLinearMap (DG_n(x)). The test forms dθ_n := exteriorDerivativeTestOn univ j θ_n and dφ := exteriorDerivativeTestOn univ j φ have underlying forms extDeriv θ_n and extDeriv φ. Hence dθ_n(x) = (dφ)(G_n x).compContinuousLinearMap (DG_n(x)) for x ∈ N_n, i.e. dθ_n is compatible with (G_n, dφ) near spt X for all large n.
6. (Limit along X.) LipPF(X, G, S) applied to (G_n), O₀, Λ, the form dφ ∈ D^{j+1}(ℝ^{m′}) and the sequence (dθ_n) gives X(dθ_n) → S(dφ), and S(dφ) = ∂S(φ) (GeometricCurrentOn.boundary_apply).
7. (Identification.) ∂X(θ_n) = X(dθ_n) for every n (GeometricCurrentOn.boundary_apply). By steps 4 and 6 and uniqueness of limits in ℝ, S_∂(φ) = ∂S(φ). Since φ was arbitrary, S_∂ = ∂S (GeometricCurrentOn.ext), and step 2 gives LipPF(∂X, G, ∂S), which is the conclusion of (II). ∎

## Key steps

1. ∂X satisfies the hypotheses of (I): finite mass, ∂∂X = 0 for the HEq condition, spt ∂X ⊆ spt X (support_lemmas) gives the Lipschitz and properness hypotheses.
2. (I) gives S_∂ with LipPF(∂X, G, S_∂).
3. With the reference sequence of (RS) for F := spt X and compatible θ_n (compatible_form), ∂X(θ_n) → S_∂(φ).
4. (dP) via extDeriv_eq on the open set N_n and extDeriv_pullback: dθ_n is compatible with (G_n, dφ), so ∂X(θ_n) = X(dθ_n) → S(dφ) = ∂S(φ).
5. Hence S_∂ = ∂S and LipPF(∂X, G, ∂S).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 over dag.json (662 nodes): statuses, lean_names, statements, candidate commits; grep of all accepted lean_statements for support/boundary-support, locality, pull-back norm, covector-norm smul, bounded-functional current criteria and extDeriv lemmas -> found iwl_cr_support_lemmas, iwl_cr_ce_apply_eq_of_eqOn_nhds_support, iwl_sp_covectorEuclideanNorm_pullback_le, fiw_ims_sc_continuous_of_bound, fiw_tb_ext_covectorNorm_smul, lpf_pic_current_of_dominated_density; no accepted 'bounded linear functional -> current with mass ≤ B' lemma (no match)`
- `python3 over nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json: frozen lean_statements of the siblings smooth_approx (889 chars), interval_product (5579), smooth_homotopy (8216), identical to dag.json`
- `rg -n 'theorem extDeriv_pullback|theorem Filter.EventuallyEq.extDeriv_eq|theorem TendstoUniformlyOn.congr_right|theorem TendstoUniformly.tendstoUniformlyOn|theorem IsCompact.cthickening|theorem mem_cthickening_of_dist_le|theorem self_subset_thickening|theorem cons_self_tail|theorem tail_cons|theorem cauchySeq_tendsto_of_complete|theorem tendsto_nhds_unique' over the snapshot mathlib/Mathlib (all found: DifferentialForm/Basic.lean:259,188; UniformSpace/UniformConvergence.lean:218,222; MetricSpace/Thickening.lean:283,201,309; Data/Fin/Tuple/Basic.lean:171,117; UniformSpace/Cauchy.lean:425; Separation/Hausdorff.lean:180)`
- `grep -n '^def|^structure|^theorem|^abbrev' over .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality}.lean: GeometricCurrentOn (toCurrent, continuous'), TestFormOnConverges, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply/boundary_boundary/ext, exteriorDerivative = extDeriv, massAdmissibleOn, massOn, mass, covectorEuclideanNorm, VanishesOn, zeroRegion, support`
- `rg -n 'dph_lpf|LipPF' over the snapshot project and mathlib (*.lean): no match; git log --all -S dph_lpf_ over 3993 refs: no match`
- `read /runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py (_existing_lean_name_problem, reuse-by-name id mapping, _dependency_problem, _overlay_accepted_children over children+depends_on) and store.py (ensure returns existing nodes unchanged)`
- `git show <candidate> for the 5 reused declarations (fd5f1e29, 02f3305f, 5c248501, ba202ac0, 3e52d3e8): declarations present together with their own accepted prerequisites; isolated-comparator-result.json passed = True for all five`
- `python3 -I verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem); verifier/lean_contract.py validate_lean_statement on all 12 child statements (all valid)`
- `lake env lean /tmp/lpf_decomp/AllStmts.lean (7 child statements + parent; only sorry warnings), /tmp/lpf_decomp/IfaceCheck.lean (parent proved from children + uncles; no errors), /tmp/lpf_decomp/Skel.lean and Endpt.lean (comparison instantiation of (E0),(E1),(Aff), compatible_form, support_lemmas; endpoint identities by rfl), /tmp/lpf_decomp/Checks3.lean (current_criterion fully proved; (dP); mass arithmetic), /tmp/lpf_review/lean/T2-T8.lean (independent full proofs of the new children modulo declared dependencies; exit 0, no errors)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-support-lemmas-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-series-current-a1-continuity-criterion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/lpf_decomp/AllStmts.lean`
- `/tmp/lpf_decomp/IfaceCheck.lean`
- `/tmp/lpf_decomp/Skel.lean`
- `/tmp/lpf_decomp/Checks3.lean`
- `/tmp/lpf_review/lean/T6.lean`
- `/tmp/lpf_review/lean/T7.lean`

The pinned project and SimonGMT contain no Lipschitz push-forward of normal currents, no products with [[0,1]] and no homotopy formula, so the supplied Parts 1–8 are new obligations. Their smooth-approximation, product and homotopy inputs come from the three unaccepted uncle nodes, which are therefore passed as explicit hypotheses. Five accepted declarations are reused by name with byte-identical types: compatible forms (R3), the support facts (S)/(F3c), the mass bound (R1), the pull-back norm bound (F7), and the continuity criterion for (F5/F6). No accepted lemma already turns a bounded linear functional into a current with a mass bound, so this becomes the new child current_criterion. Every Mathlib lemma cited in the child proofs exists in the pinned snapshot (extDeriv_pullback, EventuallyEq.extDeriv_eq, TendstoUniformlyOn.congr_right, IsCompact.cthickening, mem_cthickening_of_dist_le, self_subset_thickening, Fin.cons_self_tail, cauchySeq_tendsto_of_complete, tendsto_nhds_unique). All statements elaborate in the exact comparator scope. The parent follows from the children by a checked 4-line assembly, and each new child has an independent Lean proof modulo its declared dependencies. The dph_lpf_* names are globally unused.
