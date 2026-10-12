# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1.pointwise-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.pointwise-a1.liminf_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Steps 5 (liminf) and 6 (ε ↓ 0), extracted with a(h) := μ(W ∩ f⁻¹([t − h, t])), r := B(ω) − ∂A(ω) = −S(ω), and, for each ε > 0, X(h) the cut-off difference of the parent's Step 3 (built from the cut-offs for ε). The parent supplies the hypotheses: X(h) → r from its Step 4, and the bound from `slicing_mb_cutoff_defect_bound` together with tsupport ω ⊆ W.

Setting. a : ℝ → [0,∞]; LW ∈ ℝ≥0; r ∈ ℝ; ofReal(x) := max(x, 0) ∈ [0,∞] (ENNReal.ofReal). Hypothesis: for every ε > 0 there is X : ℝ → ℝ with X(h) → r as h → 0+ (along 𝓝[>] 0) and ofReal|X(h)| ≤ ofReal((1+ε)/h)·LW·a(h) for every h > 0 (products in [0,∞]). Put Λ := liminf_{h→0+} a(h)/ofReal(h) ∈ [0,∞] (liminf along 𝓝[>] 0) and Y := LW·Λ ∈ [0,∞] (0·∞ = 0). Claim: ofReal|r| ≤ Y.

1. (Fixed ε: the limit is a liminf.) Fix ε > 0 and take X as in the hypothesis. The map x ↦ ofReal|x| from ℝ to [0,∞] is continuous, so ofReal|X(h)| → ofReal|r| as h → 0+ (`ENNReal.tendsto_ofReal` applied to |X(h)| → |r|). The filter 𝓝[>] 0 on ℝ is nontrivial, so ofReal|r| = liminf_{h→0+} ofReal|X(h)|.

2. (Rewriting the bound.) Let h > 0. Then ofReal((1+ε)/h) = ofReal(1+ε)/ofReal(h) (`ENNReal.ofReal_div_of_pos`). Writing x/y = x·y⁻¹ and using commutativity and associativity of multiplication in [0,∞],
 ofReal((1+ε)/h)·LW·a(h) = ofReal(1+ε)·ofReal(h)⁻¹·LW·a(h) = C·(a(h)/ofReal(h)), where C := ofReal(1+ε)·LW.
 Hence ofReal|X(h)| ≤ C·(a(h)/ofReal(h)) for every h ∈ (0, ∞), and (0, ∞) ∈ 𝓝[>] 0.

3. (Passing to the liminf.) In the complete lattice [0,∞] the liminf is monotone under eventual inequalities (`liminf_le_liminf`), so by steps 1 and 2,
 ofReal|r| = liminf_{h→0+} ofReal|X(h)| ≤ liminf_{h→0+} C·(a(h)/ofReal(h)).
 C is finite (ofReal(1+ε) < ∞ and LW < ∞), and 𝓝[>] 0 is nontrivial, so multiplication by C commutes with the liminf: liminf_{h→0+} C·u(h) = C·liminf_{h→0+} u(h) (`ENNReal.liminf_const_mul_of_ne_top`; this includes C = 0, where both sides are 0). Therefore
 ofReal|r| ≤ C·Λ = ofReal(1+ε)·LW·Λ = ofReal(1+ε)·Y for every ε > 0.

4. (The factor tends to 1.) As ε → 0+, 1 + ε → 1 in ℝ, so ofReal(1+ε) → ofReal(1) = 1 in [0,∞]. Since the limit 1 is nonzero, multiplication by the constant Y ∈ [0,∞] preserves this limit (`ENNReal.Tendsto.mul_const` with the alternative 1 ≠ 0; this is valid also when Y = ∞), so ofReal(1+ε)·Y → 1·Y = Y as ε → 0+.

5. (ε ↓ 0.) By step 3, ofReal|r| ≤ ofReal(1+ε)·Y for every ε ∈ (0, ∞), a set belonging to 𝓝[>] 0, and 𝓝[>] 0 is nontrivial. Passing to the limit with step 4 (`ge_of_tendsto`) gives ofReal|r| ≤ Y = LW·liminf_{h→0+} a(h)/ofReal(h). ∎

## Key steps

1. For fixed ε > 0: ofReal|X(h)| → ofReal|r| along 𝓝[>] 0, hence ofReal|r| = liminf_{h→0+} ofReal|X(h)|.
2. For h > 0: ofReal((1+ε)/h)·LW·a(h) = (ofReal(1+ε)·LW)·(a(h)/ofReal(h)) by ofReal_div_of_pos.
3. Monotonicity of liminf and liminf of a finite constant multiple give ofReal|r| ≤ ofReal(1+ε)·(LW·Λ).
4. ofReal(1+ε)·(LW·Λ) → LW·Λ as ε → 0+ (limit factor 1 ≠ 0), so ofReal|r| ≤ LW·Λ.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Submission.lean (identical); cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical)`
- `rg -n 'IsSlice|slicing_mb' local-references/197bdd4b88278494/project (only the IsSlice definition/use in Contract.lean, Submission.lean and README.md; no slicing_mb lemma)`
- `rg -n 'theorem LipschitzOnWith.extend_real|theorem tendsto_integral_filter_of_dominated_convergence|theorem liminf_const_mul_of_ne_top|theorem ofReal_div_of_pos|theorem integral_indicator \(|theorem Tendsto.mul_const|instance nhdsGT_neBot|theorem tendsto_ofReal' local-references/197bdd4b88278494/mathlib/Mathlib`
- `grep -n 'image_eq_one_of_notMem_mulTSupport' local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean (to_additive source of image_eq_zero_of_notMem_tsupport)`
- `rg -n 'liminf.*ofReal h|ofReal_div.*liminf' local-references/197bdd4b88278494/mathlib/Mathlib (no match: no existing liminf/difference-quotient lemma of child 2's form)`
- `rg -n 'IsSlice|IsRestriction' lake-packages-25730c7c/simongmt/Poincare (no match: SimonGMT has no restriction/slice notions)`
- `grep -n 'def massAdmissibleOn|def GeometricCurrentOn.massOn|def covectorEuclideanNorm|abbrev TestFormOn|def exteriorDerivativeTestOn|theorem tsupport_exteriorDerivative_subset|theorem GeometricCurrentOn.boundary_apply|abbrev exteriorDerivative' simongmt/Poincare/SimonGMT/Chapter06/{Mass,Currents,Forms}.lean`
- `python3 read of dag.json: frozen lean_statements of slicing_mb_cutoff, slicing_mb_cutoff_defect_bound, slicing_mb_pointwise; all lean_names unique; no name with prefix slicing_mb_pointwise_ (239 nodes at last check)`
- `rg -n 'slicing_mb_pointwise_cutoff_tendsto|slicing_mb_pointwise_liminf_bound' over the snapshot project, SimonGMT and dag.json (no match)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (replayed child scope: opens, namespace GMT.Ch06, noncomputable section, end)`
- `python3 validate_lean_statement (verifier/lean_contract.py) on both child lean_statements (accepted, single line)`
- `lean --root=/tmp/pw_split_XUzTfR/src -o /tmp/pw_split_XUzTfR/out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean (scratch build of the frozen Submission, LEAN_PATH from lake env)`
- `lean /tmp/pw_split_XUzTfR/check/Stmts.lean (both child types + parent type elaborate in the comparator child scope; only sorry warnings)`
- `lean /tmp/pw_split_XUzTfR/check/Assembly.lean (exact parent type from slicing_mb_cutoff, slicing_mb_cutoff_defect_bound and both child types; #print axioms: [propext, Classical.choice, Quot.sound])`
- `lean /tmp/pw_split_XUzTfR/check/ChildProofs.lean (complete proofs of both child types; axioms [propext, Classical.choice, Quot.sound])`
- `sed -n '1340,1415p' book/chapter-06.txt (Simon Ch. 6, 4.6-4.11: statement of 4.9 and the cut-off argument of 4.11)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/DenselyOrdered.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-pointwise-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/pw_split_XUzTfR/check/Stmts.lean`
- `/tmp/pw_split_XUzTfR/check/Assembly.lean`
- `/tmp/pw_split_XUzTfR/check/ChildProofs.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the workspace Submission. IsSlice unpacks to IsRestriction data, and the restriction set {x | x ∈ U ∧ f x < t} is syntactically the set used in child 1's conclusion. SimonGMT provides massOn and massAdmissibleOn, exteriorDerivativeTestOn (whose coercion is definitionally exteriorDerivative), boundary_apply and tsupport_exteriorDerivative_subset; these are the facts the parent glue uses. Mathlib provides every lemma cited in the child proofs: LipschitzOnWith.extend_real, tendsto_integral_filter_of_dominated_convergence, integral_indicator, ENNReal.liminf_const_mul_of_ne_top, ENNReal.ofReal_div_of_pos, ENNReal.tendsto_ofReal, ENNReal.Tendsto.mul_const, the nhdsGT_neBot instance, and image_eq_zero_of_notMem_tsupport (via to_additive). It has neither child statement, and no match for a liminf difference-quotient lemma of child 2's form. Both child types and the parent type elaborate in the comparator's child scope. The exact parent type follows from the frozen sibling types slicing_mb_cutoff and slicing_mb_cutoff_defect_bound plus the two child types, with axioms [propext, Classical.choice, Quot.sound]. Both child types were also fully proved in scratch Lean with the same axioms. The proposed names are unused in the DAG, the snapshot project, SimonGMT and Mathlib. The printed Simon text (4.9, 4.11) matches the parent proof from which both child proofs are extracted.
