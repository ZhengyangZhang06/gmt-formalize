# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.projected_limit-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.projected_limit-a1.linear_pushforward_family-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 0–2 of the parent proof, specifically step 0 (p is C^∞ with fderiv ℝ p x = p), step 1 (properness), and step 2(a)–(b) (push-forward by (SPF), and the per-k mass bound from its c = 1 clause). The supremum over k of step 3, which uses sup_k (M(Z_k) + M(∂Z_k)) < ∞, stays in the parent. These steps formalize the printed Proof of 8.2 of Simon Ch. 6, from “p_#S̃_j ∈ D_n(B_1ⁿ(0))” through the mass identities (10). Here the geometric input of the parent (frame_geometry for W′, B_1ⁿ(0) and {d ≤ γ}) is replaced by the hypotheses:
   - U, V are open;
   - ‖p‖ ≤ 1 and p(U) ⊆ V;
   - p⁻¹(K) ∩ F is compact and contained in U for every compact K ⊆ V;
   - spt X_k ⊆ F.

1. (p is C^∞ with derivative p.) p is continuous linear, so it is C^∞ (ContinuousLinearMap.contDiff), and fderiv ℝ p x = p for every x (ContinuousLinearMap.fderiv). Hence ‖fderiv ℝ p x‖ = ‖p‖ ≤ 1 for every x.

2. (Properness of p on spt X_k.) Fix k and a compact K ⊆ V. By hypothesis K′ := p⁻¹(K) ∩ F is compact and K′ ⊆ U. Write Z_k := zeroRegion(X_k). It is open (GeometricCurrentOn.isOpen_zeroRegion), and spt X_k = U ∖ Z_k by definition. We claim p⁻¹(K) ∩ spt X_k = K′ ∖ Z_k.
   - “⊆”: if y ∈ p⁻¹(K) and y ∈ spt X_k, then y ∈ F (since spt X_k ⊆ F) and y ∉ Z_k. So y ∈ K′ ∖ Z_k.
   - “⊇”: if y ∈ K′ and y ∉ Z_k, then y ∈ U (since K′ ⊆ U). Hence y ∈ U ∖ Z_k = spt X_k, and y ∈ p⁻¹(K).
   K′ is compact and Z_k is open, so K′ ∖ Z_k is compact (IsCompact.diff). Therefore p⁻¹(K) ∩ spt X_k is compact for every compact K ⊆ V.

3. (Application of (SPF).) Fix k. Apply (SPF), with the hypothesis LipschitzPushforwardIntegerMultiplicity, to: P, Q; the degree index m (so X_k ∈ D_{m+1}(U)); the open sets U, V; X := X_k, which is integer multiplicity; and f := p. The hypotheses of (SPF) hold: p is C^∞ (step 1), p(U) ⊆ V, and p⁻¹(K) ∩ spt X_k is compact for every compact K ⊆ V (step 2). (SPF) yields S ∈ D_{m+1}(V) which is integer multiplicity and satisfies:
   (a) S(ω) = X_k(η) whenever ω ∈ D^{m+1}(V), η ∈ D^{m+1}(U), and η(x) = (ω(p x)).compContinuousLinearMap (fderiv ℝ p x) for all x in some open N ⊇ spt X_k;
   (b) a boundary identity, which is not needed here;
   (c) for every real c ≥ 0 with ‖fderiv ℝ p x‖ ≤ c for all x, and every W ⊆ ℝ^Q:
       M_W(S) ≤ ofReal(c^{m+1}) · M_{p⁻¹(W) ∩ U}(X_k) and M_W(∂S) ≤ ofReal(c^m) · M_{p⁻¹(W) ∩ U}(∂X_k).
   By the axiom of choice (Lean: choose), pick such an S =: S_k for every k ∈ ℕ. Each S_k is integer multiplicity.

4. (Action identity (i).) Let k, ω ∈ D^{m+1}(V) and η ∈ D^{m+1}(U) be given. Let N be open with spt X_k ⊆ N and η(x) = (ω(p x)).compContinuousLinearMap p for all x ∈ N. Since fderiv ℝ p x = p (step 1), η(x) = (ω(p x)).compContinuousLinearMap (fderiv ℝ p x) for all x ∈ N. So 3(a) gives S_k(ω) = X_k(η).

5. (Mass bounds (ii).) Fix k and W ⊆ ℝ^Q. Apply 3(c) with c := 1; this is allowed since 0 ≤ 1 and ‖fderiv ℝ p x‖ ≤ 1 for all x (step 1).
   - Since 1^{m+1} = 1^m = 1, ofReal 1 = 1 and 1·a = a, we get M_W(S_k) ≤ M_{p⁻¹(W) ∩ U}(X_k) and M_W(∂S_k) ≤ M_{p⁻¹(W) ∩ U}(∂X_k).
   - Local mass is monotone in the region (GeometricCurrentOn.massOn_mono), and p⁻¹(W) ∩ U ⊆ U. Hence M_{p⁻¹(W) ∩ U}(X_k) ≤ M_U(X_k) = M(X_k), and likewise M_{p⁻¹(W) ∩ U}(∂X_k) ≤ M_U(∂X_k) = M(∂X_k). (GeometricCurrentOn.mass T is by definition T.massOn U, for X_k and for ∂X_k ∈ D_m(U).)
   - Combining: M_W(S_k) ≤ M(X_k) and M_W(∂S_k) ≤ M(∂X_k).

6. (Conclusion.) The sequence S = (S_k)_{k∈ℕ} consists of integer multiplicity currents in D_{m+1}(V) (step 3) and satisfies (i) (step 4) and (ii) (step 5). ∎

## Key steps

1. p is C^∞ with fderiv ℝ p x = p, hence ‖fderiv ℝ p x‖ ≤ 1.
2. Properness: p⁻¹(K) ∩ spt X_k = (p⁻¹(K) ∩ F) ∖ zeroRegion(X_k), which is compact since p⁻¹(K) ∩ F is compact and contained in U.
3. Apply (SPF) with f := p for every k and choose S_k: integer multiplicity, with S_k(ω) = X_k(η) whenever η = p^#ω near spt X_k (using fderiv ℝ p = p).
4. The mass clause of (SPF) at c = 1, with massOn_mono, gives M_W(S_k) ≤ M(X_k) and M_W(∂S_k) ≤ M(∂X_k).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 scan of dag.json: parent ind_plane_multiplicity_integer children/statuses; frozen lean_statement of ind_pi_frame_geometry, ind_pi_span_integral, iwl_smooth_pushforward, ind_pi_projected_limit`
- `python3 dag.json keyword scan of lean_name/title for cutoff|urysohn|pullback|compContinuousLinearMap|smul_test|test_form|thickening and push|proj|linear|span|plane`
- `python3 dag.json: occurrences of lean_name ind_pi_pl_linear_pushforward_family (0) and iwl_sp_exists_compatible_testForm (1, accepted); cross-branch child reuse (iwl_restriction_weak_limit -> root.compactness_mass_bounds-a1.mass_bound-a1)`
- `grep -n Submission.iwl_sp_exists_compatible_testForm .swarm-worktrees/9b2e48fec405a54e7669/gmt-ch06/GMT/Ch06/Submission.lean (commit fd5f1e2)`
- `grep -n 'def \|theorem \|structure \|abbrev ' SimonGMT Chapter06/{Currents,CurrentLocalEquality,Mass,FormsDuality}.lean`
- `rg -n in snapshot mathlib: analyticOnNhd_compContinuousLinearMapCLM, exists_contDiff_support_eq_eq_one_iff, exists_contDiff_zero_iff_one_iff_of_isClosed, IsCompact.exists_cthickening_subset_open, cthickening_subset_thickening', closure_thickening_subset_cthickening, IsCompact.cthickening, self_subset_thickening, thickening_subset_cthickening, ContDiff.fderiv_right, AnalyticOnNhd.contDiff, ContDiff.clm_apply, HasCompactSupport.smul_right, tsupport_smul_subset_left, IsCompact.diff, setIntegral_congr_fun, setIntegral_eq_integral_of_forall_compl_eq_zero, Submodule.closed_of_finiteDimensional, ContinuousLinearMap.fderiv, image_eq_one_of_notMem_mulTSupport, compContinuousLinearMap_apply, zero_compContinuousLinearMap (no match)`
- `sed -n 392,416p and 2400,2490p book/chapter-06.txt (Simon 2.23 cut-off; printed Proof of 8.2, display (10))`
- `verifier lean_contract.validate_lean_statement on both child types; gmt-compare.contract_scope(Contract.lean, 'GMT.Ch06.main_theorem')`
- `lake env lean /tmp/pl-split-check-a6fc/{Scope,Stmts,Full}.lean (#print axioms chk_C2, chk_parent)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-p-a6fca12c5f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/9b2e48fec405a54e7669/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/pl-split-check-a6fc/Stmts.lean`
- `/tmp/pl-split-check-a6fc/Full.lean`

Snapshot (local-project): project d8d46c95, Mathlib 25730c7c. The workspace Submission.lean, whose contract scope is namespace GMT.Ch06 with the Contract's opens, supplies through SimonGMT: GeometricCurrentOn; support = U ∖ zeroRegion with isOpen_zeroRegion; massOn and mass (mass = massOn U) with massOn_mono; and TestFormOn.

DAG findings:
- iwl_sp_exists_compatible_testForm is accepted ('all proof gates passed'). Its frozen type is byte-identical to the reused child and is exactly steps 4–6 (the cut-off of Simon 2.23).
- No existing node provides the linear push-forward family, and ind_pi_pl_linear_pushforward_family has 0 occurrences.
- Cross-branch reuse of accepted leaves is DAG convention.
- The SPF antecedent is byte-identical to iwl_smooth_pushforward. The sibling frozen types (ind_pi_frame_geometry, ind_pi_span_integral) were used verbatim.

Mathlib: every cited lemma exists in the snapshot. image_eq_zero_of_notMem_tsupport is to_additive-generated from image_eq_one_of_notMem_mulTSupport. There is no zero_compContinuousLinearMap lemma; ext plus simp with compContinuousLinearMap_apply handles it.

Book: 2.23 and the printed Proof of 8.2 (p_#S̃_j ∈ D_n(B_1ⁿ(0)), display (10), p_#S̃_j ⇀ θ(x)[[ℝⁿ]]) match the split.

Lean: in the contract scope both child types elaborate and validate_lean_statement accepts them. The new child is proved from LPF and SPF, and the selected frozen type is proved from both children plus the two siblings. Axioms: [propext, Classical.choice, Quot.sound].
