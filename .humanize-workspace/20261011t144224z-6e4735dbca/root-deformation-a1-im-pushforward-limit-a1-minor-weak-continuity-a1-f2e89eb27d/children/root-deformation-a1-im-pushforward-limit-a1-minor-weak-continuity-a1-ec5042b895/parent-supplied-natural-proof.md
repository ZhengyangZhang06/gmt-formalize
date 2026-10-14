# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.fderiv_sum_prod-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 of the parent proof (product rule HasFDerivAt.finsetProd and linearity of the derivative).

Notation. For i ∈ ι put P_i(x) := Π_{t ∈ Fin r} g_{i,t}(x); for u ∈ Fin r put R_{i,u} := Π_{t ∈ Finset.univ.erase u} g_{i,t}(w) (the product over t ≠ u); and let L_{i,t} := fderiv ℝ g_{i,t} w, a continuous linear map ℝ^k → ℝ.

1. (Product rule.) Fix i ∈ ι. Every g_{i,t} is differentiable at w, i.e. has Fréchet derivative L_{i,t} at w (DifferentiableAt.hasFDerivAt). By the product rule for a finite product of real-valued functions (HasFDerivAt.finsetProd on the finset Finset.univ of Fin r), P_i has Fréchet derivative M_i := Σ_{u ∈ Fin r} R_{i,u} • L_{i,u} at w. (For r = 0, P_i ≡ 1 and M_i = 0, consistently.)

2. (Linearity.) Multiplying by the constant a_i (HasFDerivAt.const_mul), the function x ↦ a_i · P_i(x) has derivative a_i • M_i at w. Summing over the finite set ι (HasFDerivAt.sum on Finset.univ), the function Σ_i (x ↦ a_i · P_i(x)) has derivative M := Σ_{i ∈ ι} a_i • M_i at w; this function is F, because a finite sum of functions is evaluated pointwise (Finset.sum_apply). Hence F has Fréchet derivative M at w.

3. (Uniqueness and evaluation.) By uniqueness of the Fréchet derivative, fderiv ℝ F w = M (HasFDerivAt.fderiv). Evaluating at v, and using that finite sums and scalar multiples of continuous linear maps are evaluated termwise (sum_apply, smul_apply, smul_eq_mul),
 fderiv ℝ F w v = Σ_{i ∈ ι} a_i · Σ_{u ∈ Fin r} R_{i,u} · L_{i,u}(v).
 Finally R_{i,u} · L_{i,u}(v) = L_{i,u}(v) · R_{i,u} = (fderiv ℝ g_{i,u} w v) · Π_{t ∈ Finset.univ.erase u} g_{i,t}(w) by commutativity of multiplication in ℝ, which gives the asserted formula. ∎

Formalization notes (no new mathematics). The following script was checked with lake env lean after import GMT.Ch06.Submission in the exact comparator scope (namespace GMT.Ch06 with the frozen open commands, after the noncomputable section); it compiles without warnings and #print axioms reports only propext, Classical.choice and Quot.sound. It may be used verbatim:
theorem Submission.deformation_ipl_mwc_pi_fderiv_sum_prod : ∀ (k r : ℕ) (ι : Type) [Fintype ι] (a : ι → ℝ) (g : ι → Fin r → Eucl k → ℝ) (w v : Eucl k), (∀ i t, DifferentiableAt ℝ (g i t) w) → fderiv ℝ (fun x : Eucl k => ∑ i, a i * ∏ t, g i t x) w v = ∑ i, a i * ∑ u, fderiv ℝ (g i u) w v * ∏ t ∈ Finset.univ.erase u, g i t w := by
  intro k r ι _ a g w v hg
  have hp : ∀ i, HasFDerivAt (fun x => ∏ t, g i t x) (∑ u, (∏ t ∈ Finset.univ.erase u, g i t w) • fderiv ℝ (g i u) w) w :=
    fun i => HasFDerivAt.finsetProd (fun t _ => (hg i t).hasFDerivAt)
  have hs : HasFDerivAt (fun x => ∑ i, a i * ∏ t, g i t x) (∑ i, a i • ∑ u, (∏ t ∈ Finset.univ.erase u, g i t w) • fderiv ℝ (g i u) w) w := by
    have := HasFDerivAt.sum (u := Finset.univ) (fun i _ => (hp i).const_mul (a i))
    convert this using 1
    ext x
    simp [Finset.sum_apply]
  rw [hs.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun u _ => ?_)
  ring

## Key steps

1. Product rule (HasFDerivAt.finsetProd): P_i = Π_t g_{i,t} has derivative Σ_u (Π_{t ∈ univ.erase u} g_{i,t}(w)) • fderiv ℝ g_{i,u} w at w.
2. Linearity (HasFDerivAt.const_mul, HasFDerivAt.sum, Finset.sum_apply): F = Σ_i a_i P_i has derivative Σ_i a_i • (that sum) at w.
3. HasFDerivAt.fderiv, evaluate at v termwise (sum_apply, smul_apply, smul_eq_mul) and reorder each product by commutativity.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project, project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD (= project_commit)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both identical)`
- `python3 -I over dag.json: nodes under root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1 (piola_identity at depth 4 with no deps; minor_ibp_smooth depends on it); regex piola|hessian|schwarz|symm|cofactor|leibniz|laplace|det_|perm|sign|swap|finsetProd|fderiv_sum|prod_rule|product rule|second deriv|isSymmSnd over titles, lean names and statements; duplicate lean_name scan (none)`
- `grep deformation_ipl_mwc_pi_ over dag.json, nodes/, GMT/, the snapshot project and simongmt/Poincare; git log --all -S deformation_ipl_mwc_pi_ (no match)`
- `rg -n 'isSymmSndFDerivAt|IsSymmSndFDerivAt|det_succ_row_zero|Piola|piola|cofactor' over simongmt/Poincare and the snapshot project`
- `rg -n in the snapshot Mathlib: 'theorem det_succ_row_zero|theorem det_apply'|theorem det_transpose' (LinearAlgebra/Matrix/Determinant/Basic.lean); 'theorem ContDiffAt.isSymmSndFDerivAt|def IsSymmSndFDerivAt' (Analysis/Calculus/FDeriv/Symmetric.lean); 'theorem HasFDerivAt.finsetProd|theorem fderiv_finsetProd|theorem HasFDerivAt.const_mul' (FDeriv/Mul.lean); 'theorem fderiv_clm_apply' (FDeriv/CompCLM.lean); 'theorem HasFDerivAt.sum|theorem fderiv_sum' (FDeriv/Add.lean); 'theorem sign_mul|theorem sign_swap' (GroupTheory/Perm/Sign.lean); 'theorem prod_univ_succ' (Algebra/BigOperators/Fin.lean)`
- `lake env lean /tmp/piola_decomp/build/Avail.lean and Names.lean (#check of every cited name under import GMT.Ch06.Submission); Closure.lean (#check of the SimonGMT Chapter08 Piola lemma under the frozen import)`
- `git show 3ceb8b21a8d3961c1d9a4aad2075a7d209773632:GMT/Ch06/Submission.lean | grep (how accepted children are declared)`
- `python3 -I /tmp/piola_decomp/scripts/gen.py (verifier lean_contract.validate_lean_statement plus gmt-compare child_modules in contract mode) and lake env lean on the four /tmp/piola_decomp/build/*_challenge.lean`
- `lake env lean on /tmp/piola_decomp/build/Assembly.lean, RefImpl2.lean, RefImpl2Compare.lean and Iso_{cofactor_leibniz,hessian_symm,fderiv_sum_prod,swap_cancel}.lean, with #print axioms`
- `python3 -I /tmp/piola_decomp/scripts/build_payload.py (re-validates key and name patterns and lean statements, and embeds the verified scripts)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyPiola.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/GroupTheory/Perm/Sign.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/BigOperators/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/piola_decomp/build/Avail.lean`
- `/tmp/piola_decomp/build/Names.lean`
- `/tmp/piola_decomp/build/Closure.lean`
- `/tmp/piola_decomp/build/cofactor_leibniz_challenge.lean`
- `/tmp/piola_decomp/build/hessian_symm_challenge.lean`
- `/tmp/piola_decomp/build/fderiv_sum_prod_challenge.lean`
- `/tmp/piola_decomp/build/swap_cancel_challenge.lean`
- `/tmp/piola_decomp/build/Assembly.lean`
- `/tmp/piola_decomp/build/RefImpl2.lean`
- `/tmp/piola_decomp/build/RefImpl2Compare.lean`
- `/tmp/piola_decomp/build/Iso_cofactor_leibniz.lean`
- `/tmp/piola_decomp/build/Iso_hessian_symm.lean`
- `/tmp/piola_decomp/build/Iso_fderiv_sum_prod.lean`
- `/tmp/piola_decomp/build/Iso_swap_cancel.lean`
- `/tmp/piola_decomp/scripts/gen.py`
- `/tmp/piola_decomp/scripts/build_payload.py`

The pinned revisions are confirmed: HEAD = project_commit d8d46c95, and Contract, Submission and the snapshot Contract are byte-identical.

Nothing existing can be reused. No DAG node, no SimonGMT lemma in the frozen import closure and no Mathlib lemma states the Piola identity, the restricted Leibniz cofactor formula or the swap cancellation. SimonGMT Chapter08 ConstancyPiola (chartTangentialDivergence_coordinate_test) is a different identity, for varifold charts, and is an unknown identifier under import GMT.Ch06.Submission. Chapter06 FormsDuality only uses det_succ_row_zero for wedgeCovectors_apply_det.

Every Mathlib name the children need exists in the snapshot and elaborates under the frozen import: Matrix.det_succ_row_zero, Matrix.det_apply', Matrix.det_transpose, Fin.prod_univ_succ, Pi.single_apply, ContDiffAt.isSymmSndFDerivAt, ContDiff.fderiv_right, ContDiff.differentiable, fderiv_clm_apply, HasFDerivAt.finsetProd, HasFDerivAt.const_mul, HasFDerivAt.sum, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap, Equiv.swap_apply_of_ne_of_ne, Equiv.mulRight, Equiv.sum_comp and Fintype.sum_ite_eq. Use sum_apply and smul_apply: ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, coe_sum' and coe_smul' are deprecated.

Accepted children are declared as theorem Submission.X inside namespace GMT.Ch06. The four new names deformation_ipl_mwc_pi_{cofactor_leibniz,hessian_symm,fderiv_sum_prod,swap_cancel} collide with nothing.

Lean checks:
- All four statements validate and elaborate in the generated comparator challenge modules (exit 0).
- The parent compiles from the four sorry'd children.
- A sorry-free, warning-free reference implementation of the four children and the parent compiles.
- Each child's script compiles in isolation.
- The comparator-style exact Submission.X check passes for all five frozen types.
- #print axioms reports only propext, Classical.choice and Quot.sound.
