# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.lusin_closed-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Statement. Let n ∈ ℕ, let S ⊆ ℝⁿ be Borel, let f : ℝⁿ → (ℝⁿ)* = L(ℝⁿ, ℝ) be Borel measurable (operator-norm topology), and let ε ∈ (0, ∞]. Then there is a closed set C ⊆ ℝⁿ with C ⊆ S, Lⁿ(S ∖ C) < ε and f|C continuous.

Source. This child is the Lusin step of Simon's printed proof of Ch. 2, Theorem 1.5 (p. 44): “By Lusin's theorem (which applies to sets of infinite measure for Lⁿ) there is a closed set C ⊆ B such that ∇f|C is continuous and Lⁿ(ℝⁿ ∖ C) < ε/2”. The argument below is steps 1 and 3 of the parent proof, with the differentiability set D replaced by an arbitrary Borel set S and Dg by an arbitrary Borel map f. Finite-measure Lusin is Simon Ch. 1, Theorem 1.17.

Notation. ℝⁿ = EuclideanSpace ℝ (Fin n) with Euclidean norm |·|; B_r(x) is the open ball. Lⁿ = volume is Lebesgue measure on ℝⁿ, a locally finite, weakly regular additive Haar measure, so bounded sets have finite measure. (ℝⁿ)* = L(ℝⁿ, ℝ) carries the operator norm ‖·‖ and its Borel σ-algebra. e₁, …, e_n is the standard basis of ℝⁿ.

1. (Reduction to finite ε.) If ε > 1 (in particular if ε = ∞), it suffices to find C for the value 1 in place of ε: Lⁿ(S ∖ C) < 1 implies Lⁿ(S ∖ C) < ε. So assume 0 < ε ≤ 1; then ε is a positive real number.

2. (Annuli.) Let S₁ := {x : |x| < 1} and S_j := {x : j − 1 < |x| < j} for integers j ≥ 2.
(a) Each S_j is open, as the preimage of an open interval under the continuous map x ↦ |x|. It is bounded, since S_j ⊆ B_j(0), so Lⁿ(S_j) < ∞.
(b) The S_j are pairwise disjoint, because the intervals [0, 1), (1, 2), (2, 3), … are.
(c) Let Z := ℝⁿ ∖ ⋃_{j≥1} S_j. If x ∈ Z, then |x| is a positive integer. Indeed, if |x| < 1 then x ∈ S₁. If |x| ≥ 1 is not an integer, then j − 1 < |x| < j for j := ⌊|x|⌋ + 1 ≥ 2, so x ∈ S_j. Hence Z ⊆ ⋃_{j≥1} {x : |x| = j}, a countable union of spheres of nonzero radius. Each such sphere is Lⁿ-null (Mathlib MeasureTheory.Measure.addHaar_sphere_of_ne_zero; for n = 0 the spheres are empty). So Lⁿ(Z) = 0.

3. (Gluing fact (★).) Let F_j ⊆ S_j be closed for every j ≥ 1, and put F := ⋃_{j≥1} F_j.
(a) F is closed. Every x ∈ ℝⁿ has the neighbourhood B₁(x). If y ∈ B₁(x) ∩ S_j with j ≥ 2, then j − 1 < |y| < |x| + 1. So B₁(x) meets S_j, and hence F_j, for only finitely many j. The family (F_j) is therefore a locally finite family of closed sets, and its union is closed (Mathlib LocallyFinite.isClosed_iUnion).
(b) If a map φ is continuous on every F_j, then φ is continuous on F. Let x ∈ F, say x ∈ F_j. The open set S_j contains x, and S_j ∩ F = F_j, because F_l ⊆ S_l is disjoint from S_j for l ≠ j by 2(b). So on the relative neighbourhood S_j ∩ F of x in F, the restriction φ|F coincides with φ|F_j, which is continuous at x. Hence φ|F is continuous at x.

4. (Construction on one annulus.) Fix j ≥ 1 and let E_j := S ∩ S_j. It is Borel, and Lⁿ(E_j) ≤ Lⁿ(S_j) < ∞.
(a) Closed inner approximation. Since Lⁿ is weakly regular, every Borel set of finite measure contains closed subsets of arbitrarily small measure defect (Mathlib MeasurableSet.exists_isClosed_sdiff_lt). Choose a closed F_j ⊆ E_j with Lⁿ(E_j ∖ F_j) < ε/2^{j+3}.
(b) Lusin for the coordinates. For l = 1, …, n let g_l(x) := f(x)(e_l). The evaluation map (ℝⁿ)* → ℝ, L ↦ L(e_l), is continuous and linear, so g_l is a Borel measurable real function. Apply Lusin's theorem (Simon Ch. 1, Theorem 1.17) to g_l on the finite-measure Borel set E_j. It says that, for a Borel regular measure on a metric space, a measurable real function on a measurable set of finite measure is continuous on a closed subset whose complement in the set has arbitrarily small measure. This gives a closed C_{j,l} ⊆ E_j with Lⁿ(E_j ∖ C_{j,l}) < ε/(2^{j+3}(n+1)) such that g_l|C_{j,l} is continuous.
(c) Let C_j := F_j ∩ ⋂_{l=1}^{n} C_{j,l}; when n = 0, C_j = F_j. Then C_j is closed and C_j ⊆ E_j ⊆ S ∩ S_j. Since E_j ∖ C_j ⊆ (E_j ∖ F_j) ∪ ⋃_{l=1}^{n} (E_j ∖ C_{j,l}), subadditivity gives
Lⁿ(E_j ∖ C_j) ≤ ε/2^{j+3} + n·ε/(2^{j+3}(n+1)) ≤ 2ε/2^{j+3} = ε/2^{j+2}.
(d) f is continuous on C_j. Every g_l is continuous on C_j ⊆ C_{j,l}. For L ∈ (ℝⁿ)* and v = Σ_l v_l e_l we have |L(v)| ≤ Σ_l |v_l| |L(e_l)| ≤ |v| Σ_l |L(e_l)|, so ‖L‖ ≤ Σ_{l=1}^{n} |L(e_l)|. Applying this to L = f(x′) − f(x) gives ‖f(x′) − f(x)‖ ≤ Σ_{l=1}^{n} |g_l(x′) − g_l(x)|, which tends to 0 as x′ → x within C_j. Equivalently, use Mathlib continuousOn_clm_apply: every v is a linear combination of the e_l, so every x ↦ f(x)(v) is continuous on C_j. For n = 0 we have (ℝ⁰)* = {0}, so f is constant.

5. (Gluing.) Let C := ⋃_{j≥1} C_j. Each C_j ⊆ S_j is closed, so C is closed by 3(a). The map f is continuous on C by 3(b) and 4(d). Finally C ⊆ S, because every C_j ⊆ S.

6. (Measure estimate.) Let x ∈ S ∖ C with x ∉ Z. Then x ∈ S_j for some j, so x ∈ E_j, and x ∉ C_j because C_j ⊆ C. Hence S ∖ C ⊆ Z ∪ ⋃_{j≥1} (E_j ∖ C_j). By countable subadditivity, 2(c) and 4(c),
Lⁿ(S ∖ C) ≤ Lⁿ(Z) + Σ_{j≥1} ε/2^{j+2} = 0 + ε/4 < ε,
using 0 < ε < ∞. So C is a closed subset of S with Lⁿ(S ∖ C) < ε, and f|C is continuous. ∎

Lean notes. Finite-measure Lusin is SimonGMT Poincare.SimonGMT.Chapter01.exists_isClosed_continuousOn_of_measurable, applied with nu := volume. Its hypothesis hreg (closed inner approximation of finite-measure measurable sets) is fun _ hS hfin _ hδ => hS.exists_isClosed_sdiff_lt hfin hδ. It lives in the built module Poincare.SimonGMT.Chapter01.Lusin, which must be imported explicitly and uses only propext, Classical.choice and Quot.sound. Measurability of x ↦ f x v follows from Measurable f by fun_prop.

## Key steps

1. Reduce to finite 0 < ε ≤ 1.
2. Cover ℝⁿ, up to the Lⁿ-null spheres |x| = j, by the bounded, open, pairwise disjoint annuli S_j. Closed F_j ⊆ S_j have a closed union, and continuity on each F_j glues (★).
3. On each E_j = S ∩ S_j: a closed inner approximation F_j, plus finite-measure Lusin (Simon 1.17, SimonGMT exists_isClosed_continuousOn_of_measurable) for each coordinate x ↦ f(x)(e_l). C_j := F_j ∩ ⋂_l C_{j,l} has Lⁿ(E_j ∖ C_j) ≤ ε/2^{j+2}.
4. f is continuous on C_j because ‖L‖ ≤ Σ_l |L(e_l)| on (ℝⁿ)*.
5. C := ⋃_j C_j is closed, C ⊆ S, and f|C is continuous by (★).
6. S ∖ C ⊆ Z ∪ ⋃_j (E_j ∖ C_j), so Lⁿ(S ∖ C) ≤ ε/4 < ε.

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
