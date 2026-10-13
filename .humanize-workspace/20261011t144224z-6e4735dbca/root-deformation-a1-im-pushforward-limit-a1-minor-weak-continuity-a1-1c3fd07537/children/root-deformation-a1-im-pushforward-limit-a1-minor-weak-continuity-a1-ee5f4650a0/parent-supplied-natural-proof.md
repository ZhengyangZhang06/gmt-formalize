# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1.abs_det_le-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4(b) of the supplied proof of the selected node (“By the Leibniz formula and the triangle inequality, an n×n matrix whose entries are bounded by C in absolute value has |det| ≤ n!·C^n (prove this from Matrix.det_apply; Matrix.det_le is not imported)”), written out in full.

Notation. S_n := Equiv.Perm (Fin n) is the group of permutations of Fin n. sgn(σ) ∈ ℤˣ = {1, −1} is the sign of σ; it acts on ℝ by multiplication by ±1.

1. (Leibniz formula, Matrix.det_apply.) det A = Σ_{σ ∈ S_n} sgn(σ) • Π_{i ∈ Fin n} A_{σ(i), i}.
2. (Triangle inequality, Finset.abs_sum_le_sum_abs.) |det A| ≤ Σ_{σ ∈ S_n} |sgn(σ) • Π_i A_{σ(i), i}|.
3. (Removing the sign.) Fix σ ∈ S_n. By Int.units_eq_one_or, sgn(σ) = 1 or sgn(σ) = −1. So sgn(σ) • y is y or −y, and |sgn(σ) • y| = |y| for every real y. The absolute value is multiplicative on finite products (Finset.abs_prod), so |Π_i A_{σ(i), i}| = Π_i |A_{σ(i), i}|. Hence the σ-summand in step 2 equals Π_i |A_{σ(i), i}|.
4. (Bounding each product.) For every i ∈ Fin n, the hypothesis applied to the entry in row σ(i), column i gives |A_{σ(i), i}| ≤ c; also 0 ≤ |A_{σ(i), i}|. Finite products of nonnegative reals are monotone in each factor (Finset.prod_le_prod₀, whose hypotheses are exactly these two facts). So Π_{i ∈ Fin n} |A_{σ(i), i}| ≤ Π_{i ∈ Fin n} c = c^n, by Finset.prod_const and card (Fin n) = n. For n = 0 both products are empty and equal 1 = c^0, so no sign condition on c is used.
5. (Counting permutations.) By steps 2–4, |det A| ≤ Σ_{σ ∈ S_n} c^n = card(S_n)·c^n. By Fintype.card_perm and Fintype.card_fin, card(S_n) = (card (Fin n))! = n!. Therefore |det A| ≤ n!·c^n. ∎

Formalization note. Matrix.det_le (Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean) is not in the closure of the frozen import. Finset.prod_le_prod is the ordered-monoid version (it needs MulLeftMono, which ℝ lacks), so use Finset.prod_le_prod₀. The script below was compiled as the proof of `theorem Submission.deformation_ipl_mwc_mil_abs_det_le : <frozen type>` under `import GMT.Ch06.Submission` in the contract scope (lake env lean; #print axioms: propext, Classical.choice, Quot.sound):
  intro n c A hA
  rw [Matrix.det_apply]
  calc |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i|
      ≤ ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, |A (σ i) i| := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
          simp [h, Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), c ^ n := by
        refine Finset.sum_le_sum fun σ _ => ?_
        calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin n, c :=
              Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hA _ _)
          _ = c ^ n := by simp
    _ = (n.factorial : ℝ) * c ^ n := by
        simp [Fintype.card_perm]

## Key steps

1. Leibniz expansion det A = Σ_σ sgn(σ)·Π_i A_{σ(i),i} (Matrix.det_apply).
2. Triangle inequality over the permutation sum (Finset.abs_sum_le_sum_abs).
3. |sgn(σ)·y| = |y| since sgn(σ) = ±1, and |Π_i A_{σ(i),i}| = Π_i |A_{σ(i),i}| (Finset.abs_prod).
4. Each product Π_i |A_{σ(i),i}| ≤ c^n by monotonicity of products of nonnegative factors (Finset.prod_le_prod₀).
5. Summing n! = card(Perm (Fin n)) copies of c^n gives n!·c^n (Fintype.card_perm).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD (= project_commit)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean <snapshot>/project/GMT/Ch06/Contract.lean (both byte-identical)`
- `python3 -I over dag.json: statuses of the minor_weak_continuity-a1 children (minor_ibp_smooth-a1 and lipschitz_smooth_approx-a1 are 'decomposing', not comparator-accepted); scan of cross-branch depends_on (reuse only through accepted declarations, e.g. localization-a1 -> br_weightedTangent_congr); depth of the selected node = 4`
- `rg -n 'theorem det_le\b|theorem det_le |abs_det_le|det_sum_smul_le|theorem det_le_of' <snapshot>/mathlib/Mathlib`
- `rg -n 'deformation_ipl_mwc|abs_det_le|det_bound|ae_fderiv|fderiv_extend|extend_real' GMT <snapshot>/project lake-packages-25730c7c/simongmt/Poincare`
- `rg -n '^theorem Continuous.clm_apply|^lemma prod_le_prod₀|LipschitzOnWith.ae_differentiableWithinAt_of_mem|^theorem LipschitzOnWith.extend_real|^theorem tendsto_integral_filter_of_dominated_convergence|^theorem fderiv_of_notMem_tsupport|^theorem det_apply |^theorem measurable_fderiv_apply_const|^theorem Continuous.matrix_det|^theorem tendsto_pi_nhds' <snapshot>/mathlib/Mathlib; grep -rn 'theorem prod_le_prod' Mathlib/Algebra/Order/BigOperators`
- `#check under import GMT.Ch06.Submission (lake env lean /tmp/mil_decomp/Test0.lean, Test1.lean, Test2.lean): Matrix.det_le, Poincare.SimonGMT.Chapter02.ae_fderivWithin_eq_of_lipschitz_extension and Filter.Tendsto.clm_apply unknown; LipschitzOnWith.extend_real, LipschitzOnWith.ae_differentiableWithinAt_of_mem, norm_fderiv_le_of_lipschitz, measurable_fderiv_apply_const, tendsto_integral_filter_of_dominated_convergence, setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_congr_ae, fderiv_of_notMem_tsupport, image_eq_zero_of_notMem_tsupport, Matrix.det_apply, Continuous.matrix_det, EventuallyEq.fderiv_eq, Finset.aestronglyMeasurable_sum/prod, PiLp.norm_apply_le, ae_all_iff, Fintype.card_perm available`
- `lake env lean /tmp/mil_decomp/Children.lean (all three children proved; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/mil_decomp/Link.lean and /tmp/mil_decomp/EndToEnd.lean (selected frozen type proved from the children plus the two sibling declarations as axioms; #print axioms of the comparator-style target: propext, Classical.choice, Quot.sound, deformation_ipl_mwc_lipschitz_smooth_approx, deformation_ipl_mwc_minor_ibp_smooth)`
- `python3 -I /tmp/mil_decomp/scripts/gen.py /tmp/mil_decomp/children.json /tmp/mil_decomp/challenge (verifier lean_contract.validate_lean_statement + gmt-compare child_modules, contract mode); lake env lean /tmp/mil_decomp/challenge/{abs_det_le,det_dominated_convergence,ae_fderiv_extension}_challenge.lean (exit 0, sorry warnings only)`
- `python3 -I over the dag.json lean_name set and nodes/*/decomposition*.json for 'mwc_mil'; git --git-dir=workspaces/.github-mirror/gmt-formalize.git grep -l 'mwc_mil_' -- GMT/Ch06/Submission.lean over all 1930 Ch06 refs (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-1c3fd07537/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/mil_decomp/Children.lean`
- `/tmp/mil_decomp/Link.lean`
- `/tmp/mil_decomp/EndToEnd.lean`
- `/tmp/mil_decomp/challenge`
- `/tmp/mil_decomp/scripts/gen.py`

The pinned revisions are confirmed: HEAD equals project_commit, and Contract, Submission and the snapshot Contract are byte-identical.

No proof of this node or of its three children exists in the snapshot:
- Mathlib's Matrix.det_le exists in LinearAlgebra/Matrix/AbsoluteValue.lean but is not in the closure of the frozen import.
- SimonGMT's ae_fderivWithin_eq_of_lipschitz_extension (Chapter02/AreaDomain.lean) is an fderivWithin variant and is also outside the closure.
- Filter.Tendsto.clm_apply does not exist (only Continuous.clm_apply).
- Finset.prod_le_prod needs MulLeftMono; the ℝ version is Finset.prod_le_prod₀.

The needed tools are available under the frozen import: Rademacher (LipschitzOnWith.ae_differentiableWithinAt_of_mem), McShane (LipschitzOnWith.extend_real), dominated convergence (tendsto_integral_filter_of_dominated_convergence), Matrix.det_apply, Continuous.matrix_det, tendsto_pi_nhds, measurable_fderiv_apply_const, fderiv_of_notMem_tsupport and the set-integral lemmas.

The prerequisites minor_ibp_smooth and lipschitz_smooth_approx are not comparator-accepted, so they cannot be reused as children. They stay with the selected node's assembly, and no child needs them.

The three new names deformation_ipl_mwc_mil_* are globally unused.

Lean checks:
- All three children compile with standard axioms only.
- The link selected-node ⇐ children + two sibling declarations compiles without sorry.
- The three challenge statements elaborate in the exact comparator scope.
