# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step (3.2)(i) of the parent proof (Piola identity: “Σ_q ∂_{b(q)}[C_q(v)] = 0 … H^t is symmetric in (q,s) (Schwarz's theorem, v ∈ C²) and D_t is antisymmetric in (q,s) (exchange of rows 0 and t), so every double sum vanishes”). Here the rows 1,…,r of the parent's minor are arbitrary C² scalar functions W_0,…,W_{r−1} (in the parent W_{t} = v^{a(t+1)} = proj_{a(t+1)} ∘ v), and the argument is written with the Leibniz expansion: the antisymmetry of the determinant under the exchange of rows 0 and t+1 is the sign change of a permutation σ under σ ↦ σ∘(0 t+1). Background: L. C. Evans, Partial Differential Equations, §8.1.4(b), Lemma 1 (divergence-free rows of cofactor matrices); J. M. Ball, Arch. Rational Mech. Anal. 63 (1977) 337–403.

Notation. ℝ^k = Eucl k; e_i := EuclideanSpace.single i 1; ∂_i f(x) := fderiv ℝ f x (e_i). For a C² function f and i, j ∈ Fin k put ∂_j∂_i f(x) := fderiv ℝ (y ↦ ∂_i f(y)) x (e_j). S_n := Equiv.Perm (Fin n), sgn := Equiv.Perm.sign. Leibniz formula in row form: det M = Σ_{σ∈S_n} sgn(σ) Π_i M_{i,σ(i)} (Mathlib Matrix.det_apply is the column form Σ_σ sgn(σ) Π_i M_{σ(i),i}; apply it to the transpose and use Matrix.det_transpose).

1. (Regularity and symmetry.) Fix t ∈ Fin r. Since W_t is C², fderiv ℝ W_t is C¹, so for each i the entry function x ↦ ∂_i W_t(x) = (fderiv ℝ W_t x)(e_i) is C¹ (composition with the continuous linear evaluation at e_i), and its derivative in the direction e_j is ∂_j∂_i W_t(x) = D²W_t(x)(e_j)(e_i), where D²W_t(x) := fderiv ℝ (fderiv ℝ W_t) x. By Schwarz's theorem for C² functions over ℝ (Mathlib ContDiffAt.isSymmSndFDerivAt; minSmoothness ℝ 2 = 2), D²W_t(x)(e_j)(e_i) = D²W_t(x)(e_i)(e_j). Hence ∂_j∂_i W_t = ∂_i∂_j W_t everywhere.

2. (Cofactor formula.) Fix x ∈ ℝ^k. For y ∈ ℝ^{Fin (r+1)} let A^y be the (r+1)×(r+1) matrix whose row 0 is y and whose row t.succ (t ∈ Fin r) is (∂_{b(s′)}W_t(x))_{s′ ∈ Fin (r+1)} (rows defined by Fin.cases).
 (a) Laplace expansion along row 0 (Mathlib Matrix.det_succ_row_zero): det A^y = Σ_{j∈Fin(r+1)} (−1)^j y_j det(A^y.submatrix Fin.succ j.succAbove), and the submatrix has entries (A^y.submatrix Fin.succ j.succAbove)_{t,s} = ∂_{b(j.succAbove s)}W_t(x). For y = 𝟙_q := Pi.single q 1 every term with j ≠ q vanishes, so det A^{𝟙_q} = (−1)^q det(∂_{b(q.succAbove s)}W_t(x))_{t,s} = c_q(x).
 (b) Leibniz formula: det A^{𝟙_q} = Σ_{σ∈S_{r+1}} sgn(σ)·(𝟙_q)_{σ(0)}·Π_{t∈Fin r} ∂_{b(σ(t.succ))}W_t(x) = Σ_{σ: σ(0)=q} sgn(σ) P_σ(x), where P_σ(x) := Π_{t∈Fin r} ∂_{b(σ(t.succ))}W_t(x) (the product over the rows of Fin (r+1) splits as row 0 times the rows t.succ, Fin.prod_univ_succ).
 Hence, as functions of x,
 c_q = Σ_{σ∈S_{r+1}, σ(0)=q} sgn(σ)·P_σ.  (1)

3. (Differentiation.) Each P_σ is a finite product of the C¹ functions of Step 1, hence differentiable, and by the product rule (Mathlib HasFDerivAt.finsetProd, fderiv_finsetProd), for every direction e_j:
 fderiv ℝ P_σ w (e_j) = Σ_{u∈Fin r} ∂_j∂_{b(σ(u.succ))}W_u(w) · Π_{t∈Fin r, t≠u} ∂_{b(σ(t.succ))}W_t(w).
 By (1) and linearity of the derivative, c_q is differentiable and fderiv ℝ c_q w (e_{b(q)}) = Σ_{σ: σ(0)=q} sgn(σ)·fderiv ℝ P_σ w (e_{b(q)}). Summing over q and grouping the permutations σ ∈ S_{r+1} according to the value σ(0) (every σ lies in exactly one fibre σ(0) = q, and in that fibre b(q) = b(σ(0)); Finset.sum_fiberwise):
 Σ_q fderiv ℝ c_q w (e_{b(q)}) = Σ_{σ∈S_{r+1}} sgn(σ)·fderiv ℝ P_σ w (e_{b(σ(0))}) = Σ_{u∈Fin r} S_u,
 where S_u := Σ_{σ∈S_{r+1}} T_u(σ), T_u(σ) := sgn(σ)·H_u(σ(0), σ(u.succ))·R_u(σ), with H_u(i, j) := ∂_{b(i)}∂_{b(j)}W_u(w) for i, j ∈ Fin (r+1) and R_u(σ) := Π_{t∈Fin r, t≠u} ∂_{b(σ(t.succ))}W_t(w).

4. (Cancellation.) Fix u ∈ Fin r and let τ := Equiv.swap 0 u.succ, a transposition because 0 ≠ u.succ (Fin.succ_ne_zero). Right multiplication σ ↦ σ*τ (that is, σ∘τ) is a bijection of S_{r+1} (Equiv.mulRight τ), so S_u = Σ_σ T_u(σ∘τ) (Equiv.sum_comp). For every σ:
 (a) sgn(σ∘τ) = sgn(σ)·sgn(τ) = −sgn(σ) (Equiv.Perm.sign_mul, Equiv.Perm.sign_swap);
 (b) (σ∘τ)(0) = σ(u.succ) and (σ∘τ)(u.succ) = σ(0) (Equiv.swap_apply_left, Equiv.swap_apply_right);
 (c) if t ≠ u then t.succ ≠ 0 and t.succ ≠ u.succ (Fin.succ_injective), so (σ∘τ)(t.succ) = σ(t.succ) (Equiv.swap_apply_of_ne_of_ne), and therefore R_u(σ∘τ) = R_u(σ);
 (d) H_u(σ(u.succ), σ(0)) = H_u(σ(0), σ(u.succ)) by Step 1 (symmetry of the second derivative of W_u at w).
 Hence T_u(σ∘τ) = −T_u(σ) for every σ, so S_u = Σ_σ T_u(σ∘τ) = −Σ_σ T_u(σ) = −S_u, and S_u = 0.

5. (Conclusion.) Σ_{q∈Fin(r+1)} fderiv ℝ c_q w (e_{b(q)}) = Σ_{u∈Fin r} S_u = 0. The degenerate case r = 0 is included: then c_0 ≡ (−1)^0·det(0×0 matrix) = 1 is constant, so its derivative vanishes, in accordance with the empty sum over u ∈ Fin 0. (For k = 0 there is no map b : Fin (r+1) → Fin 0, so the statement is vacuous.) ∎

Formalization notes (no new mathematics). Every Mathlib name used above was checked to be available under the frozen `import GMT.Ch06.Submission` (do not add imports; the leaf gate rejects them): Matrix.det_succ_row_zero, Matrix.det_apply, Matrix.det_transpose, HasFDerivAt.finsetProd (the old name HasFDerivAt.finset_prod is a deprecated alias), fderiv_finsetProd, ContDiffAt.isSymmSndFDerivAt, ContDiff.continuous_fderiv, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap, Equiv.mulRight, Equiv.sum_comp, Finset.sum_involution. In Lean the sign is (-1 : ℝ) ^ (q : ℕ) and the entry derivative is fderiv ℝ (fun y => fderiv ℝ (W t) y (e_i)) x (e_j) = fderiv ℝ (fderiv ℝ (W t)) x (e_j) (e_i) (fderiv of the evaluation of a C¹ family of continuous linear maps at a constant vector).

## Key steps

1. Schwarz: the entries ∂_iW_t are C¹ and ∂_j∂_iW_t = ∂_i∂_jW_t (ContDiffAt.isSymmSndFDerivAt).
2. Cofactor formula from Laplace (det_succ_row_zero) and Leibniz expansions of the matrix with row 0 = 𝟙_q: c_q = Σ_{σ(0)=q} sgn(σ) Π_t ∂_{b(σ(t.succ))}W_t.
3. Product rule and regrouping by σ(0): Σ_q ∂_{b(q)}c_q = Σ_u Σ_σ sgn(σ) H_u(σ(0), σ(u.succ)) Π_{t≠u} ∂_{b(σ(t.succ))}W_t.
4. For each u the involution σ ↦ σ∘swap(0, u.succ) flips the sign, swaps the arguments of the symmetric H_u and fixes the other factors, so each inner sum is 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886 = git HEAD; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both byte-identical)`
- `python3 -I over dag.json: this node (depth 3, status decomposing, attempt 1, depends_on root.compactness_mass_bounds-a1.covector_expansion-a1) and the parent's decomposition-v3.json (format of reused children)`
- `python3 -I regex over dag.json titles/statements/lean statements: mollif|Piola|dense in|density of|C_c|integration by parts|weak-*|weak star|cofactor|convolution|minors|smooth approximation|ContDiffBump`
- `python3 -I over dag.json: status, candidate_commit, title/statement/lean_statement equality with the handoff for constancy_mdc_smooth_approx_identity_ae_tendsto, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_sa_mollify_lipschitz_close, cmb_covector_eq_sum_coord_smul_wedge (all accepted, equal); lean_name collisions for deformation_ipl_mwc_* (none)`
- `grep -rn deformation_ipl_mwc over GMT/, the snapshot project, simongmt/Poincare and the snapshot Mathlib (no match)`
- `rg -n 'abbrev Covector|SimonMultiIndex|def wedgeCovectors|theorem wedgeCovectors_apply_det|def euclideanCovectorCoordinate' simongmt/Poincare/SimonGMT`
- `rg -n 'theorem norm_fderiv_le_of_lipschitzOn|LipschitzOnWith.extend_real|extend_finite_dimension|lipschitzExtensionConstant' snapshot Mathlib`
- `rg -n '^theorem' Mathlib/Analysis/Calculus/Rademacher.lean and Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean; sed ContinuousMapDense.lean 135-240, LineDeriv/IntegrationByParts.lean 215-245, ContDiff/Convolution.lean 50-100 and 415-435, Matrix/AbsoluteValue.lean det_le, ContDiff/RCLike.lean lipschitzWith_of_hasCompactSupport, FDeriv/Mul.lean finsetProd`
- `git log --all -G'^import' -- GMT/Ch06/Submission.lean; git show cdfc95dc (leaf gate rejects added imports); git show 2219dd32 (accepted ae-mollifier proof uses IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub)`
- `lake env lean /tmp/mwc_decomp/build/Avail.lean, build_v2/Avail2.lean, build_v2/Avail3.lean, build_v2/Small2.lean (#check availability under import GMT.Ch06.Submission)`
- `python3 -I /tmp/mwc_decomp/gen.py (verifier lean_contract.validate_lean_statement + gmt-compare child_modules, contract mode) and lake env lean on the eleven /tmp/mwc_decomp/build_final/*_challenge.lean (all exit 0, sorry warnings only)`
- `lake env lean /tmp/mwc_decomp/build/Assembly.lean, build_v2/F_from_E.lean, build_v2/E_from_AD.lean, build_v2/RefImpl.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `grep 'Your solution is okay' in comparator-v1.log and isolated-comparator-result.json (passed: true) of the four reused nodes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/speculative-prompt-v4.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-covector-expansion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1-smooth-appro-6a720fda87/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1-smooth-appro-6a720fda87/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-fderiv-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-close-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/mwc_decomp/build_final`
- `/tmp/mwc_decomp/build/Assembly.lean`
- `/tmp/mwc_decomp/build_v2/F_from_E.lean`
- `/tmp/mwc_decomp/build_v2/E_from_AD.lean`
- `/tmp/mwc_decomp/build_v2/RefImpl.lean`
- `/tmp/mwc_decomp/build/Avail.lean`
- `/tmp/mwc_decomp/build_v2/Avail2.lean`
- `/tmp/mwc_decomp/build_v2/Avail3.lean`

Pinned revisions are confirmed (HEAD = project_commit), and Contract = Submission = the snapshot Contract byte-for-byte.
No existing proof: neither Mathlib, SimonGMT nor any accepted DAG node proves weak continuity of Jacobian minors, the Piola identity or L¹-density by smooth functions. (The r = 1 analogue slicing_im_ll_gradient_weak_star and the density node slicing_im_ll_gws_smooth_dense are not accepted.) Hence seven new children; their names deformation_ipl_mwc_* collide with nothing.
Reused, with byte-identical types and comparator-passed: cmb_covector_eq_sum_coord_smul_wedge, constancy_mdc_smooth_approx_identity_ae_tendsto, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_sa_mollify_lipschitz_close.
Import closure: the leaf gate forbids new imports (commit cdfc95dc).
- Available in the frozen closure: SimonGMT wedgeCovectors_apply_det; Mathlib norm_fderiv_le_of_lipschitzOn, LipschitzOnWith.extend_real, extend_finite_dimension, LipschitzOnWith.ae_differentiableWithinAt_of_mem, LipschitzWith.integral_lineDeriv_mul_eq, HasCompactSupport.contDiff_convolution_left/right, ContDiffAt.isSymmSndFDerivAt, HasFDerivAt.finsetProd, Matrix.det_succ_row_zero, Matrix.det_apply, measurable_fderiv(_apply_const), tendsto_integral_filter_of_dominated_convergence, IsCompact.exists_cthickening_subset_open, ContDiff.lipschitzWith_of_hasCompactSupport.
- Not available: ContDiffBump.normed and BumpFunction/Convolution, ContinuousMapDense, LineDeriv/IntegrationByParts, Matrix.det_le. The children replace them by the reused siblings or by short arguments.
Lean checks:
- All eleven statements validate and elaborate in the exact comparator scope.
- Three links compile with only propext, Classical.choice and Quot.sound: parent ⇐ coeff_minor_continuity + covector expansion; coeff_minor_continuity ⇐ minor_weak_star; minor_weak_star ⇐ test_density + minor_ibp_lipschitz.
