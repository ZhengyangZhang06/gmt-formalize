# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_local_antilipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. ℝⁿ = EuclideanSpace ℝ (Fin n), ℝ^Q = EuclideanSpace ℝ (Fin Q), B_r(w) = Metric.ball w r, and DG(z) = fderiv ℝ G z. This is the inverse-function-theorem estimate of step 5 of the parent proof, also used in Simon's proof of Ch. 3, Lemma 1.2.

1. (Lower bound for A := DG(w).) A is an injective linear map on the finite-dimensional space ℝⁿ, so there is m > 0 with |Av| ≥ m|v| for every v ∈ ℝⁿ.
- If n = 0, then v = 0 for all v and m := 1 works.
- If n ≥ 1, the unit sphere {s : |s| = 1} is compact and nonempty, and s ↦ |As| is continuous and strictly positive on it because A is injective. So m := min_{|s|=1} |As| > 0, and |Av| = |v| |A(v/|v|)| ≥ m|v| for v ≠ 0.
- In Mathlib, LinearMap.exists_antilipschitzWith gives N > 0 with |v| ≤ N|Av|; take m := 1/N.

2. (Choice of c and r.) Let c := m/2 > 0. G is C¹, so z ↦ DG(z) is continuous; choose r > 0 with ‖DG(z) − A‖ ≤ c for all z ∈ B_r(w).

3. (Mean value inequality.) Let z, z′ ∈ B_r(w).
- The map φ(y) := G(y) − A y is differentiable with Dφ(y) = DG(y) − A, so ‖Dφ(y)‖ ≤ c on the convex set B_r(w).
- By the mean value inequality (Mathlib Convex.norm_image_sub_le_of_norm_fderiv_le), |φ(z) − φ(z′)| ≤ c|z − z′|, i.e. |G(z) − G(z′) − A(z − z′)| ≤ c|z − z′|.
- Equivalently in Mathlib: G has strict derivative A at w (ContDiffAt.hasStrictFDerivAt). Then HasStrictFDerivAt.approximates_deriv_on_nhds gives a neighbourhood of w, containing a ball B_r(w), on which ApproximatesLinearOn G A (B_r(w)) c holds; that is the same estimate.

4. (Conclusion.) For z, z′ ∈ B_r(w), the reverse triangle inequality and steps 1 and 3 give |G(z) − G(z′)| ≥ |A(z − z′)| − |G(z) − G(z′) − A(z − z′)| ≥ m|z − z′| − c|z − z′| = c|z − z′|. Thus r > 0 and c > 0 satisfy c|z − z′| ≤ |G(z) − G(z′)| for all z, z′ ∈ B_r(w). ∎

## Key steps

1. Injectivity of A = DG(w) on the finite-dimensional space ℝⁿ gives m > 0 with |Av| ≥ m|v| for all v.
2. Set c := m/2; continuity of DG gives r > 0 with ‖DG(z) − A‖ ≤ c on B_r(w).
3. Mean value inequality for G − A on the convex ball: |G(z) − G(z′) − A(z − z′)| ≤ c|z − z′|.
4. Reverse triangle inequality: |G(z) − G(z′)| ≥ (m − c)|z − z′| = c|z − z′|.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project, project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD in lake-packages-25730c7c/{simongmt,mathlib} = 2b3663083f3fe399b6296fb8eaee52169170e197, 25730c7c759d108ef87ab70af2342a196760f79d`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean (identical); diff workspace Contract.lean Submission.lean (identical)`
- `python3 over dag.json: lean_name of all 90 nodes; keyword scan Whitney|Lusin|Egoroff|Egorov|Rademacher|C¹ approx|antilipschitz; assert frozen parent lean_statement byte-equal to the selected type`
- `sed -n 155,275p book/chapter-02.txt (Simon Thm 1.5, Thm 1.6 (‡), Remark 1.7, printed proof of 1.5)`
- `grep -rn 'rademacher|approximation theorem|Theorem 1.5|c1_approx|exists_contDiff_one' simongmt/Poincare/SimonGMT --include=*.lean`
- `ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter0{1,2,3} | grep olean`
- `sed -n 1,388p Chapter02/WhitneyExtension.lean; sed -n 1,227p Chapter02/WhitneyJet.lean; grep -n theorem Chapter01/Lusin.lean Chapter02/Lipschitz.lean`
- `rg -n -i lusin mathlib/Mathlib`
- `rg -n 'extend_finite_dimension|exists_antilipschitzWith|isOpen_injective|approximates_deriv_on_nhds|antilipschitzWith|exists_isClosed_sdiff_lt|exists_isClosed_lt_add|tendstoUniformlyOn_of_ae_tendsto|measurable_fderiv|measurableSet_of_differentiableAt|extend_pi|extend_real' on the snapshot mathlib/Mathlib; grep addHaar_sphere_of_ne_zero, LocallyFinite.isClosed_iUnion, LipschitzWith.ae_differentiableAt in lake-packages mathlib (same commit)`
- `python3 -I scope.py: contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py; python3 -I validate.py: lean_contract.validate_lean_statement on the 4 child statements`
- `lake env lean GMT/Ch06/Submission.lean -o .lake/build/lib/lean/GMT/Ch06/Submission.olean (scratch project, packages symlinked; find -newer confirms shared tree untouched)`
- `lake env lean Scratch/{WhitneyExtCopy,WhitneyVendored,Names,Names2,Names3,Stmts,Assembly,Vec,Small,Combined}.lean with #check and #print axioms`
- `WebSearch (standard): Evans–Gariepy Whitney extension / C¹ approximation theorem numbering (not confirmed; cite by section only)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/tmp/c1pieces_scratch/Scratch/scope_prefix.txt`
- `/tmp/c1pieces_scratch/Scratch/Stmts.lean`
- `/tmp/c1pieces_scratch/Scratch/Assembly.lean`
- `/tmp/c1pieces_scratch/Scratch/Vec.lean`
- `/tmp/c1pieces_scratch/Scratch/Small.lean`
- `/tmp/c1pieces_scratch/Scratch/Combined.lean`
- `/tmp/c1pieces_scratch/Scratch/WhitneyExtCopy.lean`
- `/tmp/c1pieces_scratch/Scratch/WhitneyVendored.lean`
- `/tmp/c1pieces_scratch/Scratch/Names.lean`
- `/tmp/c1pieces_scratch/Scratch/Names2.lean`
- `/tmp/c1pieces_scratch/Scratch/Names3.lean`
- `/tmp/c1pieces_tools/stmts.json`
- `/tmp/c1pieces_tools/gen_combined.py`

The snapshot (project d8d46c95, Mathlib 25730c7c, simongmt 2b36630) holds the frozen Ch06 Contract, byte-identical to the workspace Contract and Submission. Only the 90 existing node names are reserved in dag.json, and no node states a Whitney or C¹-approximation theorem, so lpf_c1_approximation_real, lpf_c1_approximation_eucl, lpf_c1_local_antilipschitz and lpf_lipschitz_localization are free.

Simon Ch. 2, pp. 42–44 gives Thm 1.5 and its printed proof (Rademacher, Lusin for infinite measure, η_k, Egoroff on C ∩ B_j(0), closed A ⊆ A₀) and Whitney's Thm 1.6 with condition (‡).

SimonGMT provides:
- a complete Whitney C¹ extension theorem, Chapter02.exists_contDiff_one_extension_of_whitney, with hypothesis HasWhitneyC1Compatibility (continuity on A plus a remainder bound for x ∈ compact K ⊆ A, y ∈ A); WhitneyExtension.olean is absent, but the source compiles unchanged next to import GMT.Ch06.Submission with only propext, Classical.choice and Quot.sound, so it can be vendored under GMT/Ch06/;
- Lusin, Chapter01.exists_isClosed_continuousOn_of_measurable (built; importable with standard axioms);
- Rademacher.
SimonGMT has no packaged C¹ approximation theorem.

The Mathlib snapshot has no Lusin theorem for measurable functions (only Lusin–Souslin and Lusin separation). It does provide: Egorov (tendstoUniformlyOn_of_ae_tendsto), closed inner regularity (MeasurableSet.exists_isClosed_sdiff_lt), measurable_fderiv, measurableSet_of_differentiableAt, LipschitzWith.ae_differentiableAt, addHaar_sphere_of_ne_zero, LocallyFinite.isClosed_iUnion, LipschitzOnWith.extend_finite_dimension, LinearMap.exists_antilipschitzWith, HasStrictFDerivAt.approximates_deriv_on_nhds, ContinuousLinearMap.isOpen_injective, disjointed, iUnion_disjointed and TopologicalSpace.exists_countable_basis.

All four child statements elaborate in the exact comparator child scope and pass validate_lean_statement. Scratch/Combined.lean kernel-checks the vector child from the scalar child, both small lemmas outright, and the frozen parent type from the children. Its comparator-style target uses standard axioms plus sorryAx from the scalar C¹ approximation child only.
