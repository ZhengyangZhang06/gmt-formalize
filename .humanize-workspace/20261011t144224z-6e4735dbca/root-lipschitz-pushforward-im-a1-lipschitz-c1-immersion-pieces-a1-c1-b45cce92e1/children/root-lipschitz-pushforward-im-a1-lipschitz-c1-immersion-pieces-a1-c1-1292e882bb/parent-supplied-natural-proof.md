# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.egoroff_closed-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Statement. Let n ∈ ℕ, let C ⊆ ℝⁿ be Borel, and let f_k : ℝⁿ → ℝ (k ∈ ℕ) and g : ℝⁿ → ℝ be Borel measurable with f_k(x) → g(x) for every x ∈ C. Let ε ∈ (0, ∞]. Then there is a closed set A ⊆ ℝⁿ with A ⊆ C and Lⁿ(C ∖ A) < ε such that f_k → g uniformly on A ∩ B̄_R(0) for every R ∈ ℝ.

Source. This child is the Egoroff step of Simon's printed proof of Ch. 2, Theorem 1.5 (p. 44): “by Egoroff's Theorem (applied to the finite measure sets C ∩ B_j(0), j = 1, 2, …) there is an Lⁿ-measurable set A₀ ⊆ C such that Lⁿ(C ∖ A₀) < ε/4 and η_k converges uniformly to zero on each bounded subset of A₀. Since we can take a closed set A ⊆ A₀ with Lⁿ(A₀ ∖ A) < ε/4 …”. The argument below is steps 1, 5 and 6 of the parent proof. It uses bounded open annuli instead of balls, so that the closed pieces glue. Those steps use only that the functions are Borel measurable and converge pointwise on C, so they are stated here for arbitrary Borel f_k → g.

Notation. ℝⁿ = EuclideanSpace ℝ (Fin n) with Euclidean norm |·|; B_r(x) is the open ball and B̄_R(0) = {x : |x| ≤ R}. Lⁿ = volume is Lebesgue measure on ℝⁿ, a locally finite, weakly regular additive Haar measure, so bounded sets have finite measure.

1. (Reduction to finite ε.) If ε > 1 (in particular if ε = ∞), it suffices to find A for the value 1 in place of ε. So assume 0 < ε ≤ 1; then ε is a positive real number.

2. (Annuli.) Let S₁ := {x : |x| < 1} and S_j := {x : j − 1 < |x| < j} for integers j ≥ 2.
(a) Each S_j is open (preimage of an open interval under x ↦ |x|) and bounded (S_j ⊆ B_j(0)), so Lⁿ(S_j) < ∞.
(b) The S_j are pairwise disjoint, since the intervals [0, 1), (1, 2), (2, 3), … are.
(c) Let Z := ℝⁿ ∖ ⋃_{j≥1} S_j. If x ∈ Z, then |x| is a positive integer. Indeed, if |x| < 1 then x ∈ S₁. If |x| ≥ 1 is not an integer, then j − 1 < |x| < j for j := ⌊|x|⌋ + 1 ≥ 2. So Z ⊆ ⋃_{j≥1} {x : |x| = j}. Spheres of nonzero radius are Lⁿ-null (Mathlib MeasureTheory.Measure.addHaar_sphere_of_ne_zero; for n = 0 they are empty), so Lⁿ(Z) = 0.
(d) For j ≥ 2, S_j ⊆ {x : |x| > j − 1}.
(e) Gluing (★). If F_j ⊆ S_j is closed for every j ≥ 1, then ⋃_{j≥1} F_j is closed. Every x has the neighbourhood B₁(x). If y ∈ B₁(x) ∩ S_j with j ≥ 2, then j − 1 < |y| < |x| + 1, so B₁(x) meets only finitely many S_j, hence only finitely many F_j. A locally finite union of closed sets is closed (Mathlib LocallyFinite.isClosed_iUnion).

3. (Egoroff on each annulus.) Fix j ≥ 1 and let C_j := C ∩ S_j. It is Borel, and Lⁿ(C_j) ≤ Lⁿ(S_j) < ∞. The functions f_k and g are Borel measurable real functions, hence strongly measurable, and f_k(x) → g(x) for every x ∈ C_j ⊆ C. By Egoroff's theorem on the finite-measure set C_j (Mathlib MeasureTheory.tendstoUniformlyOn_of_ae_tendsto) there is a measurable T_j ⊆ C_j with Lⁿ(T_j) ≤ ε/2^{j+3} such that f_k → g uniformly on C_j ∖ T_j.

4. (Closed inner approximation.) The set C_j ∖ T_j is Borel with finite measure. By inner regularity of Lⁿ by closed sets (Mathlib MeasurableSet.exists_isClosed_sdiff_lt) there is a closed A_j ⊆ C_j ∖ T_j with Lⁿ((C_j ∖ T_j) ∖ A_j) < ε/2^{j+3}. Since A_j ⊆ C_j ∖ T_j, f_k → g uniformly on A_j.

5. (The set A.) Let A := ⋃_{j≥1} A_j. Since A_j ⊆ C_j ⊆ S_j and A_j is closed, A is closed by 2(e). Also A ⊆ C.

6. (Measure estimate.) Let x ∈ C ∖ A with x ∉ Z. Then x ∈ S_j for some j, so x ∈ C_j. Either x ∈ T_j, or x ∈ C_j ∖ T_j and then x ∈ (C_j ∖ T_j) ∖ A_j, because x ∉ A ⊇ A_j. Hence
C ∖ A ⊆ Z ∪ ⋃_{j≥1} T_j ∪ ⋃_{j≥1} ((C_j ∖ T_j) ∖ A_j).
By countable subadditivity,
Lⁿ(C ∖ A) ≤ 0 + Σ_{j≥1} ε/2^{j+3} + Σ_{j≥1} ε/2^{j+3} = ε/8 + ε/8 = ε/4 < ε.

7. (Uniform convergence on bounded parts of A.) Let R ∈ ℝ and choose an integer J ≥ 1 with J > R. If j > J, then A_j ⊆ S_j ⊆ {x : |x| > j − 1} by 2(d), and j − 1 ≥ J > R. So A_j ∩ B̄_R(0) = ∅, and therefore A ∩ B̄_R(0) ⊆ A₁ ∪ ⋯ ∪ A_J. Let γ > 0. For each j ≤ J, uniform convergence on A_j (step 4) gives k_j such that |f_k(x) − g(x)| < γ for all k ≥ k_j and all x ∈ A_j. For k ≥ max(k₁, …, k_J) we get |f_k(x) − g(x)| < γ for all x ∈ A ∩ B̄_R(0). So f_k → g uniformly on A ∩ B̄_R(0). If R < 0 this set is empty and the claim is trivial.

8. A is closed, A ⊆ C, Lⁿ(C ∖ A) < ε, and f_k → g uniformly on A ∩ B̄_R(0) for every R ∈ ℝ. ∎

Lean notes. Egorov in the pinned Mathlib is tendstoUniformlyOn_of_ae_tendsto (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto …) (hε : 0 < ε) with ε : ℝ≥0∞. It returns t ⊆ s, MeasurableSet t, μ t ≤ ε and TendstoUniformlyOn f g atTop (s \ t). Strong measurability comes from Measurable.stronglyMeasurable, and the a.e. hypothesis from Eventually.of_forall.

## Key steps

1. Reduce to finite 0 < ε ≤ 1. Take the bounded open annuli S_j, the null set Z of spheres, and the closed gluing (★).
2. Egoroff on each finite-measure piece C_j = C ∩ S_j gives a measurable T_j ⊆ C_j with Lⁿ(T_j) ≤ ε/2^{j+3} and f_k → g uniformly on C_j ∖ T_j.
3. Closed inner approximation gives closed A_j ⊆ C_j ∖ T_j with defect < ε/2^{j+3}. A := ⋃_j A_j is closed by (★), and A ⊆ C.
4. C ∖ A ⊆ Z ∪ ⋃_j T_j ∪ ⋃_j ((C_j ∖ T_j) ∖ A_j), so Lⁿ(C ∖ A) ≤ ε/4 < ε.
5. For J > R, A ∩ B̄_R(0) ⊆ A₁ ∪ ⋯ ∪ A_J, and uniform convergence on a finite union gives uniform convergence on A ∩ B̄_R(0).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project, project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD in workspace and lake-packages-25730c7c/{simongmt,mathlib} = d8d46c95…, 2b3663083f3fe399b6296fb8eaee52169170e197, 25730c7c…`
- `cmp snapshot project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean (identical); cmp workspace Contract.lean vs Submission.lean (identical)`
- `python3 -I over dag.json: id/lean_name/status of all 200 nodes; regex scan Whitney|Lusin|Luzin|Egoroff|Egorov|Rademacher|ContDiff ℝ 1|tendstoUniformly|IsClosed; assert the selected node's lean_statement is byte-equal to the frozen type; check lpf_c1r_lusin_closed, lpf_c1r_egoroff_closed, lpf_c1r_uniform_remainder, lpf_c1r_whitney_extension are unused`
- `grep -rl 'lpf_c1r' and 'exists_contDiff_one_extension_of_whitney|WhitneyExtension' over runs/…/nodes (no other branch vendors Whitney; names free)`
- `sed -n 150,275p book/chapter-02.txt (Simon Thm 1.5, Thm 1.6 (‡), Remark 1.7, printed proof of 1.5; no printed proof of 1.6)`
- `grep -n 'Vitali|Covering Lemma|Lusin|Egoroff' book/chapter-01.txt; sed -n 340,372p and 605,640p (Lusin 1.17, 5-times Covering Lemma 3.4 with property (*))`
- `sed SimonGMT Chapter02/{WhitneyJet,WhitneyCover,WhitneyPartition,WhitneyExtension}.lean and Chapter01/Lusin.lean; grep '^theorem|^def|^structure'; ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter0{1,2} (Lusin, WhitneyJet/Cover/Partition built; WhitneyExtension.olean absent)`
- `grep in snapshot mathlib: LipschitzWith.ae_differentiableAt (Analysis/Calculus/Rademacher.lean:385), measurableSet_of_differentiableAt and measurable_fderiv (Analysis/Calculus/FDeriv/Measurable.lean:372,378), MeasurableSet.exists_isClosed_sdiff_lt (MeasureTheory/Measure/Regular.lean:1036; exists_isClosed_diff_lt deprecated), tendstoUniformlyOn_of_ae_tendsto (MeasureTheory/Function/Egorov.lean:205, ε : ℝ≥0∞), addHaar_sphere_of_ne_zero (MeasureTheory/Measure/Lebesgue/EqHaar.lean:519), LocallyFinite.isClosed_iUnion (Topology/LocallyFinite.lean:128), continuousOn_clm_apply (Analysis/Normed/Module/FiniteDimension.lean:518), norm_fderiv_le_of_lipschitz (Analysis/Calculus/FDeriv/Basic.lean:947)`
- `python3 -I scope.py (verifier gmt-compare.contract_scope → opens MeasureTheory Filter Set Metric; scoped ENNReal NNReal Topology; namespace GMT.Ch06; Chapter06/03/01 opens; noncomputable section; end); python3 -I validate.py (lean_contract.validate_lean_statement on all 4 child statements: OK)`
- `sed gmt-compare.py child_modules/candidate_inputs (generated NodeChallenge imports GMT.Ch06.Submission; new .lean files allowed under GMT/Ch06/)`
- `lean src/Submission.lean -o build/GMT/Ch06/Submission.olean in scratch /tmp/c1real-decomp with LEAN_PATH to the shared package builds (shared tree untouched)`
- `lean tests/Stmts.lean, tests/Assembly.lean, tests/Interface.lean, tests/Api.lean, tests/Combined.lean, tests/WhitneyChild.lean, tests/Verbatim.lean with #check and #print axioms; lean vend2/WhitneyExtension.lean -o build/GMT/Ch06/WhitneyExtension.olean (verbatim SimonGMT source)`
- `Agent (independent adversarial review of the four child proofs, the Lean statements and the assembly): all OK; optional wording polish applied`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyPartition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/tmp/c1real-tools/stmts.json`
- `/tmp/c1real-tools/scope.py`
- `/tmp/c1real-tools/validate.py`
- `/tmp/c1real-decomp/tests/Stmts.lean`
- `/tmp/c1real-decomp/tests/Assembly.lean`
- `/tmp/c1real-decomp/tests/Interface.lean`
- `/tmp/c1real-decomp/tests/Api.lean`
- `/tmp/c1real-decomp/tests/WhitneyChild.lean`
- `/tmp/c1real-decomp/tests/Verbatim.lean`
- `/tmp/c1real-decomp/tests/Combined.lean`
- `/tmp/c1real-decomp/vend/WhitneyVendored.lean`
- `/tmp/c1real-decomp/vend2/WhitneyExtension.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c, simongmt 2b36630) holds the frozen Ch06 Contract, byte-identical to the workspace Contract and Submission. Simon prints a proof of Thm 1.5 (p. 44) but none of Whitney's Thm 1.6.

Mathlib has no Lusin theorem for measurable functions, but provides Rademacher (LipschitzWith.ae_differentiableAt), measurableSet_of_differentiableAt, measurable_fderiv, closed inner regularity (MeasurableSet.exists_isClosed_sdiff_lt), Egorov (tendstoUniformlyOn_of_ae_tendsto, ε : ℝ≥0∞), addHaar_sphere_of_ne_zero, LocallyFinite.isClosed_iUnion, continuousOn_clm_apply and norm_fderiv_le_of_lipschitz.

SimonGMT provides:
- finite-measure Lusin, Chapter01.exists_isClosed_continuousOn_of_measurable (built; importable next to GMT.Ch06.Submission; standard axioms);
- the full Whitney C¹ extension, Chapter02.exists_contDiff_one_extension_of_whitney, whose hypothesis HasWhitneyC1Compatibility is exactly continuity of f and τ on A plus (‡). Its .olean is absent, but the source compiles verbatim as GMT/Ch06/WhitneyExtension.lean (it imports only the built WhitneyJet and WhitneyPartition), and the comparator accepts new .lean files under GMT/Ch06/.

All four child statements elaborate in the exact comparator child scope and pass validate_lean_statement. Combined.lean kernel-checks:
- the frozen parent type from the four children;
- uniform_remainder from egoroff_closed, with only the η_k facts stubbed;
- whitney_extension outright, with axioms propext, Classical.choice and Quot.sound.

The proposed lpf_c1r_* names are unused by all 200 DAG nodes and by every node artifact, and no other branch vendors Whitney.
