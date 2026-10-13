# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_eucl-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. ℝⁿ = EuclideanSpace ℝ (Fin n), ℝ^Q = EuclideanSpace ℝ (Fin Q), and Lⁿ = volume. For l ∈ Fin Q let e_l := EuclideanSpace.single l 1 be the l-th standard basis vector. Let π_l := EuclideanSpace.proj l : ℝ^Q → ℝ, π_l(y) = y_l; it is continuous linear with |π_l(y)| ≤ |y|, so ‖π_l‖ ≤ 1. Every y ∈ ℝ^Q satisfies y = Σ_l π_l(y) e_l.

This is the componentwise use of the C¹ Approximation Theorem in step 3 of the parent proof: ‘apply the claim to each component u^l, l = 1, …, Q, … and intersect the Q closed sets; if Q = 0 take A := ℝⁿ and G :≡ 0’. It uses the sibling theorem lpf_c1_approximation_real, the scalar C¹ Approximation Theorem: for K-Lipschitz g : ℝⁿ → ℝ and ε ∈ (0, ∞] there are a closed A with Lⁿ(ℝⁿ ∖ A) < ε and a C¹ h with g(x) = h(x) and HasFDerivAt g (fderiv ℝ h x) x for all x ∈ A.

1. (Splitting ε.) Choose δ ∈ (0, ∞] with Q·δ < ε:
- for Q = 0 take δ := 1, so Q·δ = 0 < ε;
- for Q ≥ 1 and ε = ∞ take δ := 1;
- for Q ≥ 1 and ε < ∞ take δ := ε/(2Q), so Q·δ = ε/2 < ε.
In Mathlib this is ENNReal.exists_pos_mul_lt.

2. (Components.) For l ∈ Fin Q let u_l := π_l ∘ u : ℝⁿ → ℝ. Since π_l is ‖π_l‖-Lipschitz and u is K-Lipschitz, u_l is (‖π_l‖·K)-Lipschitz. Apply lpf_c1_approximation_real to u_l and δ. This gives a closed A_l ⊆ ℝⁿ with Lⁿ(ℝⁿ ∖ A_l) < δ and a C¹ function h_l : ℝⁿ → ℝ such that u_l(x) = h_l(x) and HasFDerivAt u_l (fderiv ℝ h_l x) x for every x ∈ A_l.

3. (The closed set.) Let A := ⋂_l A_l, so A = ℝⁿ if Q = 0. A is closed, and ℝⁿ ∖ A = ⋃_l (ℝⁿ ∖ A_l). By finite subadditivity, Lⁿ(ℝⁿ ∖ A) ≤ Σ_l Lⁿ(ℝⁿ ∖ A_l) ≤ Q·δ < ε.

4. (The C¹ map.) Let G(x) := Σ_l h_l(x) e_l. Each map x ↦ h_l(x) e_l is a C¹ scalar function times a constant vector, hence C¹. So G is C¹ as a finite sum.

5. (Values on A.) For x ∈ A we have x ∈ A_l for all l, so u(x) = Σ_l π_l(u(x)) e_l = Σ_l u_l(x) e_l = Σ_l h_l(x) e_l = G(x).

6. (Derivatives on A.) Fix x ∈ A and let Λ ∈ L(ℝⁿ, ℝ^Q) be Λv := Σ_l (fderiv ℝ h_l x v) e_l, i.e. Λ = Σ_l (fderiv ℝ h_l x).smulRight e_l.
- Each h_l is differentiable at x, since it is C¹ and 1 ≠ 0. The sum rule and the constant-vector product rule give HasFDerivAt G Λ x, hence fderiv ℝ G x = Λ.
- On the other hand u = Σ_l u_l(·) e_l pointwise (the identity from step 5). HasFDerivAt u_l (fderiv ℝ h_l x) x holds for every l because x ∈ A_l. The same rules give HasFDerivAt u Λ x, i.e. HasFDerivAt u (fderiv ℝ G x) x.
- For Q = 0 all sums are empty (G = 0, Λ = 0, A = ℝⁿ), and the claims hold because ℝ⁰ = {0}.

By steps 3–6, A and G have all the required properties. ∎

## Key steps

1. Choose δ > 0 with Q·δ < ε.
2. Apply the scalar C¹ Approximation Theorem (sibling lpf_c1_approximation_real) to each Lipschitz component u_l = π_l ∘ u: closed A_l with Lⁿ(ℝⁿ ∖ A_l) < δ, and C¹ h_l with u_l = h_l and HasFDerivAt u_l (fderiv h_l x) x on A_l.
3. A := ⋂_l A_l is closed with Lⁿ(ℝⁿ ∖ A) ≤ Q·δ < ε.
4. G := Σ_l h_l e_l is C¹ and equals u on A.
5. Sum rule: u and G both have derivative Σ_l (fderiv h_l x).smulRight e_l at x ∈ A, so HasFDerivAt u (fderiv ℝ G x) x.

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
