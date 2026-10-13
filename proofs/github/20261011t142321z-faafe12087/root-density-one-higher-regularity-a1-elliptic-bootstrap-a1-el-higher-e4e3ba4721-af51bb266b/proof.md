# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.inner_holder-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 of the parent-supplied proof (the right side x -> Phi_k(x)[P] = <g(x), P e_k> is a fixed linear functional of g, hence C^{m,alpha}_loc), stated for an arbitrary fixed vector w = P e_k.
Notation: lam_w := innerSL R w : R^l ->L[R] R, so lam_w(v) = <w, v> = <v, w> (the real inner product is symmetric). Let f(x) := <g(x), w> and D^m := iteratedFDeriv R m.
1. f = lam_w o g pointwise (real_inner_comm).
2. C^m on U. g is C^m on U (first component of IsLocallyHolderCkα m alpha g U), and lam_w is a continuous linear map, hence C^infinity. So f = lam_w o g is C^m on U (ContinuousLinearMap.contDiff composed with ContDiffOn).
3. Derivative identity. Let x be in U. U is open, so it is a neighbourhood of x and g is C^m at x (ContDiffOn.contDiffAt). The m-th iterated derivative of a composition with a continuous linear map on the left is that map composed with the m-th iterated derivative (ContinuousLinearMap.iteratedFDeriv_comp_left with i = m <= m). Hence D^m f(x) = lam_w.compContinuousMultilinearMap (D^m g(x)).
4. Let x, y be in U. The map M -> lam_w.compContinuousMultilinearMap M is linear, so D^m f(x) - D^m f(y) = lam_w.compContinuousMultilinearMap (D^m g(x) - D^m g(y)). Moreover ||lam_w.compContinuousMultilinearMap N|| <= ||lam_w|| ||N|| (ContinuousLinearMap.norm_compContinuousMultilinearMap_le).
5. Let K be compact with K contained in U. The second component of IsLocallyHolderCkα m alpha g U gives C with ||D^m g(x) - D^m g(y)|| <= C ||x - y||^alpha for all x, y in K. Let x, y be in K; they lie in U. By steps 3-4 and ||lam_w|| >= 0, ||D^m f(x) - D^m f(y)|| <= ||lam_w|| ||D^m g(x) - D^m g(y)|| <= ||lam_w|| (C ||x - y||^alpha) = (||lam_w|| C) ||x - y||^alpha. So C' := ||lam_w|| C works. Together with step 2 this proves the claim. QED
Remark: no restriction on alpha or m is needed. For m = 0 the iterated derivative is the function itself, viewed as a 0-multilinear map, and the same computation applies.
Lean note: the following script follows steps 1-5. It compiled against the exact frozen type at the pin (Lean 4.35.0-rc3, Mathlib 25730c7c, frozen Submission imports) with no errors or warnings:
  intro n ℓ m α U g w hU hg
  set L : Rn ℓ →L[ℝ] ℝ := innerSL ℝ w with hL
  have hfun : (fun z => inner ℝ (g z) w) = L ∘ g := by
    funext z; simp [hL, real_inner_comm]
  have hiter : ∀ x ∈ U, iteratedFDeriv ℝ m (fun z => inner ℝ (g z) w) x
      = L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g x) := by
    intro x hx
    rw [hfun]
    exact L.iteratedFDeriv_comp_left (hg.1.contDiffAt (hU.mem_nhds hx)) le_rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact L.contDiff.comp_contDiffOn hg.1
  · intro K hK hKU
    obtain ⟨C, hC⟩ := hg.2 K hK hKU
    refine ⟨‖L‖ * C, fun x hx y hy => ?_⟩
    rw [hiter x (hKU hx), hiter y (hKU hy)]
    have hsub : L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g x)
        - L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g y)
        = L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y) := by
      ext v; simp
    rw [hsub]
    calc _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y‖ :=
          L.norm_compContinuousMultilinearMap_le _
      _ ≤ ‖L‖ * (C * ‖x - y‖ ^ α) := mul_le_mul_of_nonneg_left (hC x hx y hy) (norm_nonneg _)
      _ = ‖L‖ * C * ‖x - y‖ ^ α := by ring

## Key steps

1. f = innerSL R w o g by symmetry of the real inner product
2. f is C^m on U as a continuous linear image of g
3. for x in the open U: iteratedFDeriv R m f x = (innerSL R w).compContinuousMultilinearMap (iteratedFDeriv R m g x)
4. linearity and ||lam o N|| <= ||lam|| ||N|| give the Hölder bound with C' := ||innerSL R w|| * C

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `python3 -I scan of dag.json lean_name values containing dohr_eb / ehs (collision check, 431 unique names); rg -c 'dohr_eb_ehs' <snapshot>`
- `rg -n 'theorem ContinuousLinearMap.iteratedFDeriv_comp_left|theorem norm_compContinuousMultilinearMap_le|theorem contDiff_infty_iff_fderiv|theorem fderiv_clm_apply|theorem ContDiffAt.isSymmSndFDerivAt|theorem support_fderiv_subset|theorem IsCompact.uniformContinuousOn_of_continuous|theorem ContDiffOn.fderiv_of_isOpen|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem ContinuousOn.integrableOn_compact' <snapshot>/mathlib/Mathlib`
- `rg -n 'integral_add_right_eq_self|uniformContinuous_of_continuous|norm_image_sub_le_of_norm_hasFDerivWithin_le|exists_cthickening_subset_open' <snapshot>/mathlib/Mathlib`
- `lake build GMT.Ch05.Submission in scratch copy /tmp/ehs-split-1tMXHd/proj (Lean 4.35.0-rc3, .lake/packages -> shared lake-packages-25730c7c)`
- `lake env lean Checks/Types.lean (3 child types + parent type in the comparator's replayed scope: namespace GMT.Ch05, open MeasureTheory Metric Set Filter Topology, open scoped ENNReal NNReal, open RectifiableVarifold)`
- `lake env lean Checks/Assembly.lean (parent frozen type proved from the 3 child types + 4 dependency types posed as axioms; #print axioms)`
- `lake env lean Checks/Small.lean (children dohr_eb_ehs_hessian_apply_contDiff and dohr_eb_ehs_inner_right_holder proved outright)`
- `lake env lean Probe/Avail.lean and Probe/Avail2.lean (#check of every lemma cited in child 1 under the frozen imports, and with import Mathlib.Analysis.Calculus.FDeriv.Symmetric)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py, identical to the flow's copy) on the 3 child statements`
- `git show <ref>:GMT/Ch05/Submission.lean | grep '^import' for the conical-approximation solution branches (precedent for adding Mathlib imports)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean are byte-identical to the snapshot Contract. Neither the snapshot nor dag.json uses the prefix 'dohr_eb_ehs', so the three proposed names are globally fresh.

All Mathlib lemmas cited in the child proofs exist at the pin, with these locations:
- ContinuousLinearMap.iteratedFDeriv_comp_left: ContDiff/Basic.lean:255.
- ContinuousLinearMap.norm_compContinuousMultilinearMap_le: Normed/Module/Multilinear/Basic.lean:919.
- contDiff_infty_iff_fderiv: ContDiff/Defs.lean:1266.
- ContDiffOn.fderiv_of_isOpen: ContDiff/Defs.lean:907.
- fderiv_clm_apply: FDeriv/CompCLM.lean:143.
- ContDiffAt.isSymmSndFDerivAt: FDeriv/Symmetric.lean:533.
- support_fderiv_subset: FDeriv/Const.lean:379.
- IsCompact.uniformContinuousOn_of_continuous: HeineCantor.lean:49.
- HasCompactSupport.uniformContinuous_of_continuous: to_additive of HeineCantor.lean:91.
- IsCompact.exists_cthickening_subset_open: Thickening.lean:426.
- setIntegral_eq_integral_of_forall_compl_eq_zero: Bochner/Set.lean:486.
- ContinuousOn.integrableOn_compact: LocallyIntegrable.lean:592.
- norm_image_sub_le_of_norm_hasFDerivWithin_le: MeanValue.lean:422.
- integral_add_right_eq_self: used at Rademacher.lean:190.

Under the frozen Submission imports every one of these resolves except ContDiffAt.isSymmSndFDerivAt and second_derivative_symmetric_of_eventually. Child 1 must therefore add `import Mathlib.Analysis.Calculus.FDeriv.Symmetric`. The conical-approximation solution branches already add Mathlib imports to Submission.lean, so this has precedent. With that import, minSmoothness ℝ 2 = 2 closes by simp.

Lean checks on the scratch build:
- The 3 child types and the frozen parent type elaborate in the comparator scope.
- With the 3 child types and the 4 dependency types posed as axioms, the parent type is proved. #print axioms lists propext, Classical.choice, Quot.sound and exactly those 7.
- Children 2 and 3 are proved outright.

The snapshot contains no elliptic or difference-quotient regularity theory that could replace child 1. 'difference quotient' only appears in UniformLimitsDeriv.lean, as recorded in the parent handoff.
