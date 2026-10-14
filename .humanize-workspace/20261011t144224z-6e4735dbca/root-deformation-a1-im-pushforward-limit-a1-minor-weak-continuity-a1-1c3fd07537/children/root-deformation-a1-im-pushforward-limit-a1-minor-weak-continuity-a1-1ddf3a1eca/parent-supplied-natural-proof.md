# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1.ae_fderiv_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6(a)–(b) of the supplied proof of the selected node (“Since Ω is an open neighbourhood of w on which ṽ^c = v^c, the two functions agree near w, so fderiv ℝ ṽ^c w = fderiv ℝ v^c w … By Rademacher's theorem on Ω … v is differentiable at λ-a.e. w ∈ Ω. At such w the chain rule for the continuous linear map EuclideanSpace.proj c gives fderiv ℝ v^c w = (EuclideanSpace.proj c).comp (fderiv ℝ v w)”). Here g replaces the McShane extension ṽ^c; only the equality g = v^c on Ω is used.

Notation. π := EuclideanSpace.proj c, a continuous linear map ℝ^Q →L[ℝ] ℝ; v^c := π ∘ v; λ := Lebesgue measure (volume) on ℝ^k.

1. (Rademacher's theorem on Ω.) ℝ^k and ℝ^Q are finite-dimensional real normed spaces, λ is an additive Haar measure on ℝ^k, and v is C-Lipschitz on Ω. So Mathlib's LipschitzOnWith.ae_differentiableWithinAt_of_mem gives: for λ-a.e. w, if w ∈ Ω then v is differentiable within Ω at w. Fix such a w with w ∈ Ω, and fix x ∈ ℝ^k. It suffices to prove fderiv ℝ g w x = π(fderiv ℝ v w x) for this w and x.
2. (Within implies at.) Ω is open and w ∈ Ω, so Ω is a neighbourhood of w (IsOpen.mem_nhds). Differentiability within a neighbourhood of w is differentiability at w (DifferentiableWithinAt.differentiableAt). So v is differentiable at w, i.e. HasFDerivAt v (fderiv ℝ v w) w.
3. (Locality.) g and v^c agree on Ω, a neighbourhood of w, so g =ᶠ[𝓝 w] v^c (Filter.eventuallyEq_of_mem). The Fréchet derivative depends only on the germ at w, so fderiv ℝ g w = fderiv ℝ v^c w (Filter.EventuallyEq.fderiv_eq). This holds whether or not g is differentiable at w.
4. (Chain rule.) A continuous linear map is its own derivative at every point (ContinuousLinearMap.hasFDerivAt): HasFDerivAt π π (v w). Composing with step 2 (HasFDerivAt.comp) gives HasFDerivAt (π ∘ v) (π ∘L fderiv ℝ v w) w. Hence fderiv ℝ v^c w = π ∘L fderiv ℝ v w (HasFDerivAt.fderiv).
5. (Evaluation.) By steps 3 and 4, fderiv ℝ g w x = (π ∘L fderiv ℝ v w) x = π(fderiv ℝ v w x) = EuclideanSpace.proj c (fderiv ℝ v w x). Here w was an arbitrary point of Ω in the conull set of step 1, and x was arbitrary. So the stated property holds for λ-a.e. w. ∎

Formalization note. The script below was compiled as the proof of `theorem Submission.deformation_ipl_mwc_mil_ae_fderiv_eq_proj : <frozen type>` under `import GMT.Ch06.Submission` in the contract scope (lake env lean; #print axioms: propext, Classical.choice, Quot.sound):
  intro k Q Ω C v c g hΩ hv hg
  filter_upwards [hv.ae_differentiableWithinAt_of_mem (μ := volume)] with w hw hwΩ x
  have hd : DifferentiableAt ℝ v w := (hw hwΩ).differentiableAt (hΩ.mem_nhds hwΩ)
  have heq : g =ᶠ[𝓝 w] (fun w => EuclideanSpace.proj c (v w)) :=
    Filter.eventuallyEq_of_mem (hΩ.mem_nhds hwΩ) hg
  rw [heq.fderiv_eq]
  have := ((EuclideanSpace.proj c).hasFDerivAt.comp w hd.hasFDerivAt).fderiv
  rw [show (fun w => EuclideanSpace.proj c (v w)) = (EuclideanSpace.proj c) ∘ v from rfl, this]
  rfl

## Key steps

1. Rademacher on Ω (LipschitzOnWith.ae_differentiableWithinAt_of_mem): for a.e. w ∈ Ω, v is differentiable within Ω at w.
2. Ω open, so differentiability within Ω at w is differentiability at w.
3. g = proj_c ∘ v on the neighbourhood Ω of w, so fderiv ℝ g w = fderiv ℝ (proj_c ∘ v) w (EventuallyEq.fderiv_eq).
4. Chain rule for the continuous linear proj_c: fderiv ℝ (proj_c ∘ v) w = proj_c ∘L fderiv ℝ v w.
5. Evaluate at x: fderiv ℝ g w x = proj_c (fderiv ℝ v w x).

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
