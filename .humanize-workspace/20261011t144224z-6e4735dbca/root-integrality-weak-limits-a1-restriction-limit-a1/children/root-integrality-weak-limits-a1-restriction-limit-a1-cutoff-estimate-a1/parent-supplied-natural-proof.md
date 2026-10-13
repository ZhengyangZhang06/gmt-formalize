# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.restriction_limit-a1`
- Child DAG node: `root.integrality_weak_limits-a1.restriction_limit-a1.cutoff_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions.
- ℝ^P := Eucl P; |α| := covectorEuclideanNorm α for a k-covector α.
- D^k(U) := TestFormOn U k is a real vector space under pointwise operations, and every element has tsupport ⊆ U. D_k(U) := GeometricCurrentOn U k consists of linear functionals on D^k(U).
- M_V(Z) := Z.massOn V ∈ [0, ∞]. A finite element m of [0, ∞] is identified with the real number m.toReal.
- A_s := {x ∈ U : φ(x) < s}; W_t := {x ∈ W : φ(x) < t} for t ∈ ℝ; W″ := {x ∈ W : a < φ(x)}.
- IsRestriction Y A S means: A is measurable, and there are a measure μ₀ and v₀ : ℝ^P → NVector(ℝ^P, k) such that
  - IsMeasureRepresentation Y μ₀ v₀: for every η ∈ D^k(U), x ↦ v₀(x)(η(x)) is μ₀-integrable and Y(η) = ∫ v₀(x)(η(x)) dμ₀(x);
  - S(η) = ∫_A v₀(x)(η(x)) dμ₀(x) for every η ∈ D^k(U).
  Each v₀(x) is a continuous linear functional on k-covectors.

Source: steps 3 and 5 of the parent proof (P6), 'A cutoff adapted to s' and 'Error estimate', for a single current Y and a given cutoff pair (ω, ω′ = χω). Step 5 is carried out slightly differently:
- S is evaluated through its own representation (μ₀, v₀), which is also a representation of Y.
- (F1), the sibling mass_bound, is applied to S on the open set W″.
- The mass identity gives M_{W″}(S) = μ(W″ ∩ A_s) = μ(W ∩ {a < φ < s}). This is the parent's μ_Y(W ∩ B_η) with a = s − η.
This avoids forming the restriction to B_η and comparing restrictions computed from different representations.

Proof.
1. (Unpacking.) By IsRestriction Y A_s S, the set A_s is measurable, and there are μ₀, v₀ with IsMeasureRepresentation Y μ₀ v₀ and S(η) = ∫_{A_s} v₀(x)(η(x)) dμ₀(x) for all η ∈ D^k(U).
2. (Y is its own restriction to ℝ^P.)
   - ℝ^P is measurable, and for η ∈ D^k(U), ∫_{ℝ^P} v₀(x)(η(x)) dμ₀ = ∫ v₀(x)(η(x)) dμ₀ = Y(η) (Measure.restrict_univ). Hence IsRestriction Y ℝ^P Y holds via (μ₀, v₀).
   - The hypothesis on μ with A = ℝ^P and S′ = Y gives M_{W′}(Y) = μ(W′ ∩ ℝ^P) = μ(W′) for every open W′ ⊆ U.
3. (Open sets.)
   - φ is continuous on W, because W ⊆ U.
   - W is open, so W_t = W ∩ φ⁻¹((−∞, t)) for t ∈ ℝ and W″ = W ∩ φ⁻¹((a, ∞)) are open (ContinuousOn.isOpen_inter_preimage). All of them lie in W ⊆ U.
   - By step 2, M_{W_s}(Y) = μ(W_s) and M_{W_a}(Y) = μ(W_a).
4. (S(ω′) = Y(ω′).) Let x ∉ A_s.
   - If x ∈ U, then φ(x) ≥ s, so ω′(x) = 0 by hypothesis (1).
   - If x ∉ U, then x ∉ tsupport ω′ because tsupport ω′ ⊆ U, so ω′(x) = 0.
   In both cases v₀(x)(ω′(x)) = v₀(x)(0) = 0, since v₀(x) is linear. So the integrand of S(ω′) vanishes off A_s, and S(ω′) = ∫_{A_s} v₀(ω′) dμ₀ = ∫ v₀(ω′) dμ₀ = Y(ω′) (setIntegral_eq_integral_of_forall_compl_eq_zero).
5. (Measure bookkeeping.) Let D := W″ ∩ A_s = {x ∈ W : a < φ(x) < s}, using W ⊆ U.
   - D and W_a are disjoint, since φ > a on D and φ < a on W_a.
   - W_a is measurable, because it is open.
   - Both lie in W_s: points of D are in W with φ < s, and points of W_a have φ < a < s.
   Hence μ(D) + μ(W_a) = μ(D ∪ W_a) ≤ μ(W_s) (measure_union, measure_mono).
   By step 3 and monotonicity of mass, μ(W_s) = M_{W_s}(Y) ≤ M_W(Y) < ∞ and μ(W_a) = M_{W_a}(Y) ≤ M_W(Y) < ∞. So m := μ(D) is finite as well, since m ≤ m + μ(W_a) ≤ μ(W_s).
   Applying toReal to the inequality (ENNReal.toReal_mono, ENNReal.toReal_add) gives, as real numbers, m ≤ μ(W_s) − μ(W_a) = M_{W_s}(Y) − M_{W_a}(Y).
6. (Mass of S on W″.) S is a restriction of Y to A_s, and W″ is an open subset of U. So the hypothesis on μ gives M_{W″}(S) = μ(W″ ∩ A_s) = m = ENNReal.ofReal(m.toReal), the last equality because m is finite.
7. (c ≥ 0.) 0 ≤ |ω(0) − ω′(0)| ≤ c, by hypothesis (3).
8. (Basic mass estimate: sibling mass_bound = cmb_abs_apply_le_of_massOn_le.) D^k(U) is a vector space, so ω − ω′ ∈ D^k(U) with (ω − ω′)(x) = ω(x) − ω′(x). Apply mass_bound with T := S, the test form ω − ω′, the set W″, B := m.toReal ≥ 0 and C := c. Its hypotheses hold:
   - M_{W″}(S) ≤ ENNReal.ofReal(m.toReal), by step 6;
   - tsupport(ω − ω′) ⊆ W″, by hypothesis (2);
   - |(ω − ω′)(x)| = |ω(x) − ω′(x)| ≤ c for all x, by hypothesis (3).
   Hence |S(ω − ω′)| ≤ m.toReal·c.
9. (Conclusion.) S is linear, so by step 4, S(ω) − Y(ω′) = S(ω) − S(ω′) = S(ω − ω′). By steps 8, 5 and 7, |S(ω) − Y(ω′)| = |S(ω − ω′)| ≤ c·m ≤ c·(M_{W_s}(Y) − M_{W_a}(Y)). ∎

Lean remark, verified in scratch: `rw [map_sub]` does not fire on `S (ω - ω')`; use `(S.toCurrent.map_sub ω ω').symm` together with `Submodule.coe_sub`/`Pi.sub_apply` for the coerced difference.

## Key steps

1. The representation (μ₀, v₀) of S also represents Y, so Y is its own restriction to ℝ^P and M_{W′}(Y) = μ(W′) for every open W′ ⊆ U.
2. ω′ vanishes off A_s, hence S(ω′) = Y(ω′) and S(ω) − Y(ω′) = S(ω − ω′).
3. M_{W″}(S) = μ(W ∩ {a < φ < s}) ≤ μ(W_s) − μ(W_a) = M_{W_s}(Y) − M_{W_a}(Y), by disjointness and finiteness.
4. The basic mass estimate (mass_bound) on W″ ⊇ tsupport(ω − ω′), with |ω − ω′| ≤ c, gives |S(ω − ω′)| ≤ c·M_{W″}(S).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Contract.lean (identical); cmp project/GMT/Ch06/Submission.lean project/GMT/Ch06/Contract.lean (identical)`
- `rg -n -i -l helly mathlib/Mathlib project (in the snapshot)`
- `rg -n 'massOn_iUnion|massOn_iSup|iwl_rl_' project mathlib/Mathlib lake-packages-25730c7c/simongmt/Poincare`
- `rg -n "theorem exists_contDiff_zero_iff_one_iff_of_isClosed|theorem normal_exists_closure_subset|theorem IsCompact.tendsto_subseq |theorem isCompact_univ_pi|theorem IsCompact.elim_directed_cover|theorem Monotone.countable_not_continuousAt|theorem tendsto_atTop_iSup|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem setIntegral_congr_fun |theorem ContinuousOn.preimage_isClosed_of_isClosed|theorem ContinuousOn.isOpen_inter_preimage|theorem tendsto_pi_nhds|theorem liminf_le_of_frequently_le'|theorem tsupport_smul_subset_right" mathlib/Mathlib (snapshot)`
- `grep -n '^variable' mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean (smoothness order n : ℕ∞, so (n := ⊤) is C^∞)`
- `grep -n '^def |^theorem |^abbrev ' simongmt Chapter06/{Currents,Forms,Mass,FormsDuality}.lean (TestFormOn, GeometricCurrentOn, WeaklyConvergesOn, massAdmissibleOn, massOn, massOn_mono, le_massOn, massOn_le_liminf, covectorEuclideanNorm, NVector)`
- `python3 scan of dag.json (235 nodes): lean_name/lean_statement/status, accepted reuse candidates, foreign-child linking precedent`
- `grep -l <each new name> nodes/*/*.json dag.json DAG.md; git log --all -S iwl_rl_`
- `git show b9f9acdc41eaa29f36e54d7e570ae94d8ca8b4a6 / ba202ac0407b6e93210594416fcd0729874b2eff / c34586955a827a6731d9bc0ca8ae1ba1c0791948 :GMT/Ch06/Submission.lean`
- `grep -n 'selection argument|6.7(2)|4.5(1)' book/chapter-06.txt; sed -n 1512,1545p book/chapter-02.txt`
- `python3 gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') + lean_contract.validate_lean_statement on the 6 child types`
- `lake build GMT.Ch06.Submission (scratch /tmp/iwl-rl-v3-LB0u7K, frozen sources, pinned lake-packages-25730c7c)`
- `lake env lean Scratch/Challenges/Challenge_<name>.lean (6 files)`
- `lake env lean Scratch/Assembly.lean`
- `lake env lean Scratch/CutoffTry.lean; lake env lean Scratch/Children.lean`
- `lake build GMT.Ch06.Submission (candidate = b9f9acd Submission + br_la_testForm_covectorNorm_bounded + 4 new children + parent); lake env lean Scratch/Solutions.lean (exact Submission.<name>; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convex/Radon.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/MonotoneConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-limit-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-limit-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-limit-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-testform-bounded-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-testform-bounded-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/iwl-rl-v3-LB0u7K/Scratch/Challenges`
- `/tmp/iwl-rl-v3-LB0u7K/Scratch/Assembly.lean`
- `/tmp/iwl-rl-v3-LB0u7K/Scratch/CutoffTry.lean`
- `/tmp/iwl-rl-v3-LB0u7K/Scratch/Children.lean`
- `/tmp/iwl-rl-v3-LB0u7K/GMT/Ch06/Submission.lean`
- `/tmp/iwl-rl-v3-LB0u7K/Scratch/Solutions.lean`

Snapshot (project d8d46c95, Mathlib 25730c7c): the frozen Ch06 Contract is byte-identical to the workspace copy, and the snapshot Submission is byte-identical to the Contract.

Mathlib supplies every tool the children use:
- isCompact_univ_pi, IsCompact.tendsto_subseq and tendsto_pi_nhds;
- Monotone.countable_not_continuousAt and normal_exists_closure_subset;
- exists_contDiff_zero_iff_one_iff_of_isClosed (smooth Urysohn; n : ℕ∞, so ⊤ means C^∞);
- tsupport_smul_subset_right, IsCompact.elim_directed_cover and tendsto_atTop_iSup;
- setIntegral_eq_integral_of_forall_compl_eq_zero and setIntegral_congr_fun;
- ContinuousOn.isOpen_inter_preimage, ContinuousOn.preimage_isClosed_of_isClosed and liminf_le_of_frequently_le'.
SimonGMT supplies massOn, massOn_mono, le_massOn and WeaklyConvergesOn.massOn_le_liminf.

No match was found for:
- a Helly selection theorem (rg 'helly' finds only Analysis/Convex/Radon.lean, the convex Helly theorem);
- massOn_iUnion or massOn_iSup;
- any iwl_rl_* name in the project, Mathlib, SimonGMT, dag.json (235 nodes), other proposals or git history.

Accepted reuse: cmb_abs_apply_le_of_massOn_le (ba202ac) and br_la_testForm_covectorNorm_bounded (c345869) are accepted with comparator_passed=true, and their DAG types are string-identical to the proposed children.

Scratch verification:
- All 6 child types elaborate in the comparator child scope with only the intended sorry.
- The parent assembly compiles from stubs.
- The 4 new children are fully proved.
- With the accepted reuse proofs and the accepted iwl_restriction_theory (b9f9acd), the exact frozen parent Submission.iwl_restriction_weak_limit compiles.
- `exact Submission.<name>` checks pass, and #print axioms gives only propext, Classical.choice and Quot.sound for all 8 declarations.

The book's 8.2 proof and Remark 8.3(1) (chapter-06 lines 2313 and 2431) cite '4.5(1) and a selection argument as in 6.7(2) of Ch. 2'.

These checks do not replace the child acceptance gates.
