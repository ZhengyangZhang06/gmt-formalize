# Parent-supplied natural-language proof

- Parent DAG node: `root.c1_approximation-a1`
- Child DAG node: `root.c1_approximation-a1.remainder_modulus-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Introduction to GMT, Ch. 2, proof of Theorem 1.5 (printed p. 44), printed: "On C we define h(x) = f(x), ν(x) = ∇f(x) and R(x,y) for x, y ∈ C is as defined in 1.6(*). Evidently (since C ⊆ B) we have lim_{y→x, y∈C} R(x,y) = 0 for all x ∈ C, but not necessarily uniformly with respect to x on compact subsets of C as in 1.6(*). We therefore proceed as follows. For each k = 1, 2, … let η_k(x) = sup{|R(x,y)| : y ∈ C ∩ B_{1/k}(x)∖{x}}. Then η_k ↓ 0 pointwise in C, …". Here 1.6(*) is R(x,y) = (h(y) − h(x) − ν(x)·(y − x))/|x − y|. Egoroff's theorem, used next in the printed proof, needs η_k to be measurable. The printed proof leaves this implicit; the parent proof supplies it (Part II, step 4(c)) by taking the supremum over a countable dense subset D of C. Below, η_k is defined directly as this countable supremum, with radius 1/(k+1) for k = 0, 1, 2, …. It is Borel for an arbitrary set C. At points of C it is the printed supremum taken over the open ball of radius 1/(k+1); Simon's B_ρ(x) is the closed ball. Hence printed η_{k+2} ≤ η_k ≤ printed η_{k+1} on C (see the remark after step 5). Notation: ℝⁿ = EuclideanSpace ℝ (Fin n), |·| the Euclidean norm, ⟨·,·⟩ the inner product. The hypothesis "f is differentiable at x with derivative v ↦ ⟨ν(x), v⟩" is HasFDerivAt f (innerSL ℝ (ν x)) x, and innerSL ℝ (ν x) v = ⟨ν(x), v⟩ (Mathlib innerSL_apply_apply).

1. Remainder quotient. For x, q ∈ ℝⁿ put ρ(x,q) := |f(q) − f(x) − ⟨ν(x), q − x⟩| / |q − x|, with the convention t/0 := 0 (so ρ(x,x) = 0); for q ≠ x this is |R(x,q)|. Since f is K-Lipschitz and |⟨ν(x), q − x⟩| ≤ |ν(x)||q − x| (Cauchy–Schwarz), |f(q) − f(x) − ⟨ν(x), q − x⟩| ≤ (K + |ν(x)|)|q − x|. Hence 0 ≤ ρ(x,q) ≤ K + |ν(x)| for all x, q.

2. Countable dense subset. ℝⁿ is a separable metric space, so every subset of it is separable. Hence there is a countable D ⊆ C with C ⊆ closure(D) (Mathlib TopologicalSpace.IsSeparable.exists_countable_dense_subset, Metrizable/Basic.lean:185). In particular D = ∅ iff C = ∅.

3. Definition of η_k. For k ∈ ℕ let r_k := 1/(k+1) and, for q ∈ D, let U_{k,q} := {x : 0 < |q − x| < r_k}, an open set. Put φ_{k,q}(x) := ρ(x,q) if x ∈ U_{k,q} and φ_{k,q}(x) := 0 otherwise. Define η_k(x) := sup_{q∈D} φ_{k,q}(x), with sup ∅ := 0 (Lean's iSup over an empty index in ℝ is 0). By step 1, for each x the family (φ_{k,q}(x))_{q∈D} lies in [0, K + |ν(x)|], so it is bounded above. Consequently: (a) if D ≠ ∅, then φ_{k,q}(x) ≤ η_k(x) for every q ∈ D (le_ciSup), and 0 ≤ η_k(x); (b) if c ≥ 0 and φ_{k,q}(x) ≤ c for all q ∈ D, then η_k(x) ≤ c (ciSup_le when D ≠ ∅; η_k(x) = 0 when D = ∅).

4. Measurability. Fix k and q ∈ D. The map x ↦ f(q) − f(x) − ⟨ν(x), q − x⟩ is Borel: f is continuous, x ↦ ν(x) and x ↦ q − x are Borel, and the inner product is continuous (Mathlib Measurable.inner). Also x ↦ |q − x| is continuous, so x ↦ ρ(x,q) is Borel as a quotient of Borel real functions. Since U_{k,q} is open, φ_{k,q} = indicator of U_{k,q} times ρ(·,q) is Borel. As D is countable, η_k = sup_{q∈D} φ_{k,q} is a countable supremum of Borel real functions, hence Borel (Mathlib Measurable.iSup, BorelSpace/Order.lean:909, for the countable index type D).

5. Property (i). Let k ∈ ℕ and x, y ∈ C with 0 < |y − x| < r_k. Since y ∈ closure(D), there are q_ℓ ∈ D with q_ℓ → y; in particular D ≠ ∅. As ℓ → ∞, |q_ℓ − x| → |y − x| ∈ (0, r_k), so there is ℓ_0 with 0 < |q_ℓ − x| < r_k for all ℓ ≥ ℓ_0. For such ℓ we have x ∈ U_{k,q_ℓ}, so ρ(x,q_ℓ) = φ_{k,q_ℓ}(x) ≤ η_k(x) by 3(a). The map q ↦ ρ(x,q) is continuous at q = y, because y ≠ x and f is continuous. Hence ρ(x,y) = lim_ℓ ρ(x,q_ℓ) ≤ η_k(x). Multiplying by |y − x| > 0 gives |f(y) − f(x) − ⟨ν(x), y − x⟩| = ρ(x,y)|y − x| ≤ η_k(x)|y − x|.
Remark: since every q ∈ D is in C, it follows that η_k(x) = sup{|R(x,y)| : y ∈ C, 0 < |y − x| < r_k} for x ∈ C. This is the printed η_{k+1}(x) with the closed ball B_{1/(k+1)}(x) replaced by the open ball. Hence printed η_{k+2}(x) ≤ η_k(x) ≤ printed η_{k+1}(x) for x ∈ C. This comparison is not used below.

6. Property (ii). Let x ∈ C and suppose HasFDerivAt f (innerSL ℝ (ν x)) x. Then f(y) − f(x) − ⟨ν(x), y − x⟩ = o(|y − x|) as y → x. Let δ > 0. There is r > 0 with |f(y) − f(x) − ⟨ν(x), y − x⟩| ≤ δ|y − x| whenever |y − x| < r. Choose k_0 ∈ ℕ with r_{k_0} ≤ r and let k ≥ k_0 and q ∈ D. If x ∈ U_{k,q}, then 0 < |q − x| < r_k ≤ r_{k_0} ≤ r, so φ_{k,q}(x) = ρ(x,q) ≤ δ. Otherwise φ_{k,q}(x) = 0 ≤ δ. By 3(a) and 3(b), 0 ≤ η_k(x) ≤ δ for all k ≥ k_0 (when D = ∅, η_k(x) = 0). Hence η_k(x) → 0 as k → ∞.

7. Conclusion. The sequence (η_k)_{k∈ℕ} consists of Borel functions (step 4), satisfies (i) (step 5) and satisfies (ii) (step 6). ∎

Remark (optional simplification). Step 2 may instead take D countable and dense in all of ℝⁿ (Mathlib TopologicalSpace.exists_countable_dense). Steps 3–6 then go through verbatim, except the comparison remark after step 5, which uses D ⊆ C and is not needed. Step 5 uses only C ⊆ closure(D), and step 6 uses only the differentiability estimate, which holds for all y near x. With this choice D ≠ ∅, so the case D = ∅ disappears. A kernel-checked scratch proof of this child statement uses this choice.

## Key steps

1. Remainder quotient ρ(x,q) = |f(q) − f(x) − ⟨ν(x),q − x⟩|/|q − x| satisfies 0 ≤ ρ ≤ K + |ν(x)|.
2. Choose a countable D ⊆ C dense in C (separability of ℝⁿ).
3. η_k(x) := sup over q ∈ D of 1{0<|q−x|<1/(k+1)}·ρ(x,q) (sup ∅ = 0); a bounded countable supremum of Borel functions, hence Borel.
4. (i) For x, y ∈ C with 0 < |y−x| < 1/(k+1), approximate y by q_ℓ ∈ D; continuity of ρ(x,·) at y ≠ x gives ρ(x,y) ≤ η_k(x).
5. (ii) If f has derivative ⟨ν(x),·⟩ at x, the o(|y−x|) estimate bounds every term by δ once 1/(k+1) ≤ r, so η_k(x) → 0.

## Reference use

### local-project

Queries:
- `rg -n 'theorem LipschitzWith.ae_differentiableAt' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `rg -n '^theorem measurableSet_of_differentiableAt |^theorem measurable_fderiv ' mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `rg -n 'exists_isClosed_sdiff_lt|exists_isClosed_diff_lt' mathlib/Mathlib`
- `rg -n 'theorem tendstoUniformlyOn_of_ae_tendsto' mathlib/Mathlib`
- `rg -n -i 'lusin|luzin' mathlib/Mathlib`
- `rg -n 'theorem Measurable.iSup |theorem IsSeparable.exists_countable_dense_subset|theorem LocallyFinite.isClosed_iUnion|theorem addHaar_sphere ' mathlib/Mathlib`
- `sed -n 510,530p mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean; sed -n 95,115p mathlib/Mathlib/Topology/LocallyFinite.lean`
- `rg -n 'theorem innerSL_apply|innerSL_apply_apply|theorem toDual_symm_apply' mathlib/Mathlib/Analysis/InnerProductSpace`
- `rg -n 'theorem continuous_toLp|theorem continuous_ofLp' mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `rg -n 'theorem continuousWithinAt_inter |theorem continuousOn_pi |theorem measure_iUnion_le |theorem ae_iff |theorem tendstoUniformlyOn_iff ' mathlib/Mathlib`
- `rg -n '^def C1Approximation|^def WhitneyExtension|^def Rademacher|^theorem main_theorem' project/GMT/Ch02/Contract.lean; rg -n '1.5: ' project/GMT/Ch02/README.md`
- `rg -n -i 'lusin|egorov|egoroff' project/`
- `rg -n 'theorem exists_isClosed_continuousOn_of_measurable' -A 25 lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean; rg -n 'instance' (same file)`
- `rg -o '"lean_name": "[^"]*"' -g '*.json' <run dir> (name-collision check)`
- `python3 -I gen_checks.py (replays verifier gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement for the 3 lean_statements); lake env lean checks/NodeChallenge_00..02.lean against a scratch olean of GMT.Ch02.Submission`
- `lake env lean checks/Assembly.lean (#print axioms assembly_check); lake env lean checks/LibCompat.lean; lake env lean checks/Review_adv_child1.lean checks/Review_adv_child02.lean checks/Review_adv_child2_noLusin.lean; python3 -I cmp_stmts.py (verbatim statement comparison)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-approximation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-01-source.txt`
- `/tmp/c1approx-decomp-zCiTNz/checks/Assembly.lean`
- `/tmp/c1approx-decomp-zCiTNz/checks/LibCompat.lean`
- `/tmp/c1approx-decomp-zCiTNz/checks/NodeChallenge_00.lean`
- `/tmp/c1approx-decomp-zCiTNz/checks/NodeChallenge_01.lean`
- `/tmp/c1approx-decomp-zCiTNz/checks/NodeChallenge_02.lean`
- `/tmp/c1approx-decomp-zCiTNz/checks/Review_adv_child1.lean`
- `/tmp/c1approx-decomp-zCiTNz/checks/Review_adv_child02.lean`

Contract.lean:199 (C1Approximation), :191 (Rademacher) and :208 (WhitneyExtension) fix the parent and sibling types. The snapshot Mathlib has every library fact the three children and the parent glue need: LipschitzWith.ae_differentiableAt (Rademacher.lean:385), measurableSet_of_differentiableAt and measurable_fderiv (FDeriv/Measurable.lean:372, :378), MeasurableSet.exists_isClosed_sdiff_lt (Regular.lean:1036; the WeaklyRegular instance for volume on Rn n is found), tendstoUniformlyOn_of_ae_tendsto (Egorov.lean:205), Measurable.iSup (BorelSpace/Order.lean:909), IsSeparable.exists_countable_dense_subset (Metrizable/Basic.lean:185), LocallyFinite.isClosed_iUnion and LocallyFinite.continuousOn_iUnion (LocallyFinite.lean:103), addHaar_sphere_of_ne_zero (EqHaar.lean:519; addHaar_sphere needs [Nontrivial] and fails for variable n), innerSL_apply_apply (LinearMap.lean:172; innerSL_apply does not exist), toDual_symm_apply (Dual.lean:178), PiLp.continuous_toLp (PiLp.lean:546), continuousWithinAt_inter, continuousOn_pi, measure_iUnion_le and ae_iff. No-match results: Mathlib has no continuity Lusin theorem (rg 'lusin' finds only Lusin separation and Lusin–Souslin in Polish/Basic.lean), and the project snapshot has no σ-finite or vector-valued Lusin, no closed-set Egorov and no remainder-modulus lemma. These three obligations are therefore new children. The finite-measure real Lusin theorem is the pinned SimonGMT lemma Poincare.SimonGMT.Chapter01.exists_isClosed_continuousOn_of_measurable (Lusin.lean:127). It uses only propext, Classical.choice and Quot.sound, declares no instances, and instantiates for volume on Rn n with hreg := MeasurableSet.exists_isClosed_sdiff_lt. It needs `import Poincare.SimonGMT.Chapter01.Lusin` in Submission.lean; the Ch01 contract imports the same module. Using the comparator's own contract_scope/child_modules code, all three lean_statements elaborate after import GMT.Ch02.Submission, and the generated NodeChallenge_00..02 compile. Assembly.lean proves C1Approximation from LipschitzExtension ∧ Rademacher, WhitneyExtension and the three verbatim child types, using only the standard axioms. Scratch Lean proofs of all three child statements (verbatim types) compile with only the standard axioms. dag.json and the decompositions already written by other branches contain no c1approx_* names.
