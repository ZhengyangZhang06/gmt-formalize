# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_smooth-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_smooth-a1.integral_fderiv_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 4 of the parent proof of deformation_ipl_mwc_minor_ibp_smooth (“A directional derivative of a compactly supported C¹ function has integral 0”). The parent proves it with Mathlib's integration by parts for Lipschitz functions, using the constant function 1 as partner. Here it is stated for an arbitrary C¹ compactly supported h : ℝ^k → ℝ and an arbitrary direction e ∈ ℝ^k.

Notation.
- ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k), a finite-dimensional real normed space.
- λ := volume is Lebesgue measure on ℝ^k. It is an additive Haar measure (Mathlib instance Measure.IsAddHaarMeasure).
- For g : ℝ^k → ℝ and w, v ∈ ℝ^k, lineDeriv ℝ g w v is the derivative at t = 0 of t ↦ g(w + t·v) (Mathlib's lineDeriv). It is defined to be 0 when that derivative does not exist.

1. (h is Lipschitz.) h is C¹ with compact support, and the smoothness order 1 is ≠ 0. Mathlib's ContDiff.lipschitzWith_of_hasCompactSupport (hypotheses in the order HasCompactSupport h, ContDiff ℝ 1 h, 1 ≠ 0) gives some D ∈ ℝ≥0 such that h is D-Lipschitz on ℝ^k. Mathematically: Dh is continuous with compact support, hence bounded by some D, and the mean value inequality gives |h(x) − h(y)| ≤ D·|x − y|.

2. (Partner function.) Let f : ℝ^k → ℝ be the constant function f(w) = 1. It is Lipschitz with constant 0 (LipschitzWith.const).

3. (Integration by parts for Lipschitz functions.) Mathlib's LipschitzWith.integral_lineDeriv_mul_eq (Mathlib/Analysis/Calculus/Rademacher.lean) states the following. Let E be finite-dimensional with an additive Haar measure μ, let f be Lipschitz, let g be Lipschitz with compact support, and let v ∈ E. Then
 ∫ lineDeriv ℝ f x v · g(x) dμ(x) = ∫ lineDeriv ℝ g x (−v) · f(x) dμ(x).
Apply it with E = ℝ^k, μ = λ, the function f of Step 2, g := h (Lipschitz by Step 1, compactly supported by hypothesis) and v := e:
 ∫ lineDeriv ℝ f w e · h(w) dλ(w) = ∫ lineDeriv ℝ h w (−e) · f(w) dλ(w).   (∗)

4. (The left side of (∗) is 0.) For every w ∈ ℝ^k, the constant function f is differentiable at w with fderiv ℝ f w = 0 (differentiableAt_const, fderiv_const). By DifferentiableAt.lineDeriv_eq_fderiv, lineDeriv ℝ f w e = fderiv ℝ f w e = 0. So the left integrand is 0·h(w) = 0 for every w, and the left side of (∗) is ∫ 0 dλ = 0 (integral_zero).

5. (The right side of (∗).) Since h is C¹ and 1 ≠ 0, h is differentiable at every w ∈ ℝ^k (ContDiff.differentiable). By DifferentiableAt.lineDeriv_eq_fderiv and linearity of the continuous linear map fderiv ℝ h w:
 lineDeriv ℝ h w (−e) = fderiv ℝ h w (−e) = −fderiv ℝ h w e.
Since f(w) = 1, the right integrand equals −fderiv ℝ h w e for every w. By integral_neg (which needs no integrability hypothesis), the right side of (∗) equals −∫ fderiv ℝ h w e dλ(w).

6. (Conclusion.) By (∗) and Steps 4–5, 0 = −∫ fderiv ℝ h w e dλ(w), so ∫ fderiv ℝ h w e dλ(w) = 0. No case distinction on k is needed: ℝ^0 is still finite-dimensional and λ is still an additive Haar measure there, so Steps 1–6 apply verbatim. ∎

Formalization notes. Checked under the frozen `import GMT.Ch06.Submission`; do not add imports. Mathlib's LineDeriv/IntegrationByParts file (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable) is NOT in the import closure. The following script proves the exact frozen type, using only the axioms propext, Classical.choice and Quot.sound:
  intro k h e hh hcs
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hh one_ne_zero
  have h1 : LipschitzWith 0 (fun _ : Eucl k => (1 : ℝ)) := LipschitzWith.const 1
  have key := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure (Eucl k))) h1 hD hcs e
  have hl1 : ∀ x, lineDeriv ℝ (fun _ : Eucl k => (1 : ℝ)) x e = 0 := by
    intro x
    rw [(differentiableAt_const (1 : ℝ)).lineDeriv_eq_fderiv]
    simp
  have hl2 : ∀ x, lineDeriv ℝ h x (-e) = -fderiv ℝ h x e := by
    intro x
    rw [((hh.differentiable one_ne_zero) x).lineDeriv_eq_fderiv]
    simp
  simp only [hl1, hl2, zero_mul, integral_zero, mul_one, integral_neg] at key
  linarith

## Key steps

1. h is Lipschitz: ContDiff.lipschitzWith_of_hasCompactSupport (C¹, compact support, 1 ≠ 0).
2. LipschitzWith.integral_lineDeriv_mul_eq with f ≡ 1 (Lipschitz with constant 0), g = h, v = e and μ = volume (additive Haar measure on the finite-dimensional Eucl k): ∫ lineDeriv f w e · h(w) = ∫ lineDeriv h w (−e) · 1.
3. The line derivative of the constant function equals fderiv of a constant = 0, so the left side is 0.
4. h is differentiable, so lineDeriv ℝ h w (−e) = fderiv ℝ h w (−e) = −fderiv ℝ h w e, and the right side is −∫ fderiv ℝ h w e (integral_neg).
5. Therefore ∫ fderiv ℝ h w e dλ = 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886 = git rev-parse HEAD; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both identical)`
- `python3 -I over dag.json: nodes under minor_weak_continuity (status, lean_name, depends_on); regex over titles/statements/lean statements: lineDeriv|integral_lineDeriv|directional derivative|integration by parts|Laplace expansion|det_succ_row_zero|cofactor|Piola|HasCompactSupport.*fderiv; statements concluding ContDiff of Matrix.det or ∫ …, fderiv … = 0 (none)`
- `python3 -I over dag.json: lean_name collision check for deformation_ipl_mwc_mis_integral_fderiv_eq_zero and deformation_ipl_mwc_mis_det_contDiff (free; re-checked at 656 nodes, including the new minor_ibp_lipschitz children abs_det_le, ae_fderiv_extension, det_dominated_convergence and the test_density child scalar_dense)`
- `rg -n 'deformation_ipl_mwc_mis|integral_fderiv_eq_zero|det_contDiff' GMT/ local-references/197bdd4b88278494/project lake-packages-25730c7c/simongmt/Poincare and snapshot Mathlib (no match)`
- `grep -n 'theorem|lemma' Mathlib/Analysis/Calculus/Rademacher.lean; sed -n 30,105p and 160,205p (LipschitzWith.integral_lineDeriv_mul_eq; section variables FiniteDimensional ℝ E, μ.IsAddHaarMeasure)`
- `grep -rn 'theorem contDiff_prod|ContDiff.sum|contDiff_det|ContDiff.det|ContDiff.*Matrix.det' snapshot Mathlib (contDiff_prod and ContDiff.sum in ContDiff/Operations.lean; no determinant-smoothness lemma)`
- `rg -n '^theorem' Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean; lake env lean /tmp/mis_decomp/NotAvail.lean (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable and integral_bilinear_fderiv_right_eq_neg_left_of_integrable unknown under the frozen import)`
- `git show 50ef52b3 (accepted slicing_im_ll_gws_lipschitz_ibp: Submission.X declaration layout; its IBP only gives an existential g, so it cannot replace child 1)`
- `lake env lean /tmp/mis_decomp/Avail.lean (#check of ContDiff.lipschitzWith_of_hasCompactSupport, LipschitzWith.integral_lineDeriv_mul_eq, DifferentiableAt.lineDeriv_eq_fderiv, Matrix.det_apply', Matrix.det_succ_row_zero, contDiff_prod, ContDiff.sum, ContDiff.fderiv_right, ContDiff.clm_apply, tsupport_fderiv_subset, integral_finsetSum)`
- `lake env lean /tmp/mis_decomp/Children.lean (both children proved; axioms propext, Classical.choice, Quot.sound)`
- `python3 -I /tmp/mis_decomp/scripts/gen.py (verifier lean_contract.validate_lean_statement + gmt-compare child_modules, contract mode); lake env lean /tmp/mis_decomp/build/*_challenge.lean (exit 0, sorry warning only) and *_solution_emulated.lean (standard axioms)`
- `lake env lean /tmp/mis_decomp/Assembly.lean (parent frozen type from Piola + both child types as hypotheses; axioms propext, Classical.choice, Quot.sound); python3 -I /tmp/mis_decomp/scripts/link.py + lake env lean /tmp/mis_decomp/build/Link.lean (real Submission names; sorryAx only from the Piola stub)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-327766afed/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-327766afed/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-327766afed/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/mis_decomp/Avail.lean`
- `/tmp/mis_decomp/NotAvail.lean`
- `/tmp/mis_decomp/Children.lean`
- `/tmp/mis_decomp/Assembly.lean`
- `/tmp/mis_decomp/children.json`
- `/tmp/mis_decomp/scripts/gen.py`
- `/tmp/mis_decomp/scripts/link.py`
- `/tmp/mis_decomp/build/Link.lean`
- `/tmp/mis_decomp/build/integral_fderiv_zero_challenge.lean`
- `/tmp/mis_decomp/build/det_contdiff_challenge.lean`
- `/tmp/mis_decomp/build/integral_fderiv_zero_solution_emulated.lean`
- `/tmp/mis_decomp/build/det_contdiff_solution_emulated.lean`

Pinned revisions confirmed: HEAD = project_commit d8d46c95, and Contract = Submission = the snapshot Contract byte for byte.
No existing declaration does the job. Mathlib's C¹ integration-by-parts file (LineDeriv/IntegrationByParts) is outside the frozen import closure, and no Mathlib, SimonGMT or accepted DAG node proves that ∫ fderiv h · e = 0 for compactly supported C¹ h, or that a determinant of C^m entries is C^m. The accepted slicing_im_ll_gws_lipschitz_ibp only provides an existential divergence g, so it does not apply.
Both children are therefore new, and their names (deformation_ipl_mwc_mis_*) collide with nothing.
Available under the frozen import (and used): ContDiff.lipschitzWith_of_hasCompactSupport, LipschitzWith.integral_lineDeriv_mul_eq, DifferentiableAt.lineDeriv_eq_fderiv, Matrix.det_apply', Matrix.det_succ_row_zero, contDiff_prod, ContDiff.sum, ContDiff.fderiv_right, ContDiff.clm_apply, tsupport_fderiv_subset, Continuous.integrable_of_hasCompactSupport, integral_finsetSum.
Lean checks: both statements validate and elaborate in the comparator scope, and both children are proved with standard axioms. The parent's frozen type follows from the frozen piola_identity type plus the two children with only propext, Classical.choice and Quot.sound.
