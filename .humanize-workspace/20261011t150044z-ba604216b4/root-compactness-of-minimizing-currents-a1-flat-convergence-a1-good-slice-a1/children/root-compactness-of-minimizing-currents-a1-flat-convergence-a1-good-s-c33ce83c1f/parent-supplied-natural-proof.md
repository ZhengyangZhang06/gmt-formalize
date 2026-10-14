# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1.helly_no_concentration-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0–3, and the ε = ∞ case of step 8, of the parent-supplied proof of cmc_fc_good_slice. That is Helly's selection argument, which realizes elementarily the compactness/atom-counting ingredient of Simon Ch. 6, proof of 7.2 ("by 4.5(1),(2) and an argument as in 6.7(2) of Ch. 2"). One harmless adjustment: the countable set D = ℚ ∩ (a, b) itself indexes the Tychonoff product, so neither an enumeration of D nor the hypothesis a < b is needed. If b ≤ a, then (a, b) = ∅ and the final claim is vacuous; the argument runs verbatim with D possibly empty.

1. (Restriction.) For j ∈ ℕ let ν_j := μ_j⌞[a, b], i.e. ν_j(E) = μ_j(E ∩ [a, b]) for Borel E ⊆ ℝ. Then ν_j(ℝ) = μ_j([a, b]) ≤ Λ < ∞. So each ν_j is a finite Borel measure with ν_j(E) ≤ Λ for every Borel E, and ν_j(E) = μ_j(E) for every Borel E ⊆ [a, b].

2. (Helly selection.) Let D := {d ∈ ℚ : a < d < b}, a countable set. For j ∈ ℕ define v_j : D → ℝ by v_j(d) := ν_j([a, d]).toReal. Since 0 ≤ ν_j([a, d]) ≤ ν_j(ℝ) ≤ Λ < ∞ and toReal is monotone on finite values, v_j(d) ∈ [0, Λ.toReal]. Thus every v_j lies in K := Π_{d∈D} [0, Λ.toReal] ⊆ ℝ^D. K is compact by Tychonoff (Mathlib isCompact_univ_pi). ℝ^D is a countable product of second countable spaces, so it is second countable and hence first countable. Therefore (Mathlib IsCompact.tendsto_subseq) there are G ∈ K and a strictly increasing φ : ℕ → ℕ with v_{φ(j)} → G in ℝ^D. Convergence in the product topology is coordinatewise (Mathlib tendsto_pi_nhds), so
  (2.1) ν_{φ(j)}([a, d]).toReal → G(d) as j → ∞, for every d ∈ D.
From G ∈ K, 0 ≤ G(d) ≤ Λ.toReal for every d ∈ D. If d, d' ∈ D and d ≤ d', then [a, d] ⊆ [a, d'], so ν_j([a, d]).toReal ≤ ν_j([a, d']).toReal for every j (both values are finite). Limits preserve non-strict inequalities, so passing to the limit in (2.1) gives G(d) ≤ G(d').

3. (Limit distribution function.) For t ∈ ℝ let A_t := {0} ∪ {G(d) : d ∈ D, d < t} and G̃(t) := sup A_t. A_t is nonempty and bounded above by Λ.toReal, so G̃(t) is a well-defined real number. If t ≤ t', then A_t ⊆ A_{t'}, hence G̃(t) ≤ G̃(t'). So G̃ : ℝ → ℝ is nondecreasing, and therefore the set
  N := {t ∈ ℝ : G̃ is not continuous at t}
is countable (Mathlib Monotone.countable_not_continuousAt). Moreover:
 (α) if d ∈ D and d < t, then G(d) ∈ A_t, so G(d) ≤ G̃(t);
 (β) if d ∈ D and t < d, then G̃(t) ≤ G(d). Indeed every element of A_t is ≤ G(d): the element 0 satisfies 0 ≤ G(d), and an element G(d') with d' ∈ D, d' < t satisfies d' < d, hence G(d') ≤ G(d) by step 2.

4. (The claim.) We show that φ from step 2 (strictly increasing) and N from step 3 (countable) satisfy the conclusion. Let s ∈ (a, b) with s ∉ N, so G̃ is continuous at s, and let ε ∈ (0, ∞]. If ε = ∞, then δ := 1 > 0 works, since every value of a measure is ≤ ∞. Assume from now on that ε < ∞, and put e := ε.toReal. Then e > 0 because 0 < ε < ∞, and ENNReal.ofReal(e) = ε.

5. (Choice of δ.) By continuity of G̃ at s, choose η₀ > 0 such that |G̃(t) − G̃(s)| < e/2 whenever |t − s| < η₀. Put η := min(η₀/3, (s − a)/3, (b − s)/2). Since s − a > 0 and b − s > 0, η > 0, and 2η < η₀, 2η < s − a and s + η < b. By density of ℚ in ℝ (Mathlib exists_rat_btwn), choose rationals d₁, d₂ with s − 2η < d₁ < s − η and s < d₂ < s + η. Then a < s − 2η < d₁ < s < b and a < s < d₂ < s + η < b, so d₁, d₂ ∈ D and d₁ < s < d₂. By (β) with t = s − 2η < d₁, G̃(s − 2η) ≤ G(d₁). By (α) with d₂ < s + η = t, G(d₂) ≤ G̃(s + η). Since |(s + η) − s| = η < η₀ and |(s − 2η) − s| = 2η < η₀, we have G̃(s + η) < G̃(s) + e/2 and G̃(s − 2η) > G̃(s) − e/2. Consequently
  (5.1) G(d₂) − G(d₁) ≤ G̃(s + η) − G̃(s − 2η) < e.
Set δ := η > 0.

6. (Mass bound for each j.) Fix j. Since a < s − 2η < s − δ and s < b, [s − δ, s] ⊆ [a, b], so μ_j([s − δ, s]) = ν_j([s − δ, s]) by step 1. Further, [s − δ, s] ⊆ [a, d₂] ∖ [a, d₁]: a point x with s − δ ≤ x ≤ s satisfies a < x ≤ s < d₂ and x ≥ s − η > d₁. Since d₁ < d₂, [a, d₁] ⊆ [a, d₂]; as ν_j([a, d₁]) < ∞, additivity gives
  ν_j([a, d₂] ∖ [a, d₁]) = ν_j([a, d₂]) − ν_j([a, d₁]) = ENNReal.ofReal(x_j),
where x_j := ν_j([a, d₂]).toReal − ν_j([a, d₁]).toReal is a difference of finite values whose subtracted term is the smaller one. By monotonicity of ν_j,
  (6.1) μ_j([s − δ, s]) ≤ ENNReal.ofReal(x_j).

7. (Eventual smallness.) By (2.1), x_{φ(j)} → G(d₂) − G(d₁) as j → ∞, and this limit is < e by (5.1). Hence x_{φ(j)} < e for all sufficiently large j. For every such j, (6.1) and monotonicity of ENNReal.ofReal give μ_{φ(j)}([s − δ, s]) ≤ ENNReal.ofReal(x_{φ(j)}) ≤ ENNReal.ofReal(e) = ε. So δ > 0 and μ_{φ(j)}([s − δ, s]) ≤ ε for all sufficiently large j. Together with the case ε = ∞ of step 4, this proves the claim for every s ∈ (a, b) ∖ N and every ε ∈ (0, ∞], with φ strictly increasing and N countable. ∎

## Key steps

1. Restrict to [a, b]: ν_j := μ_j⌞[a, b] is a finite Borel measure with ν_j(ℝ) ≤ Λ that agrees with μ_j on Borel subsets of [a, b].
2. Tychonoff on Π_{d∈ℚ∩(a,b)} [0, Λ.toReal] and first countability of the countable product give a strictly increasing φ and G with ν_{φ(j)}([a, d]).toReal → G(d) for every rational d ∈ (a, b). G is monotone with values in [0, Λ.toReal].
3. G̃(t) := sup({0} ∪ {G(d) : d < t}) is nondecreasing, so its discontinuity set N is countable. Also G(d) ≤ G̃(t) for d < t, and G̃(t) ≤ G(d) for t < d.
4. The case ε = ∞ is trivial. Otherwise, at a continuity point s ∈ (a, b) ∖ N, choose η > 0 and rationals d₁ ∈ (s − 2η, s − η), d₂ ∈ (s, s + η) with G(d₂) − G(d₁) < ε.toReal, and put δ := η.
5. μ_j([s − δ, s]) ≤ ν_j([a, d₂] ∖ [a, d₁]) = ofReal(ν_j([a, d₂]).toReal − ν_j([a, d₁]).toReal). Along φ this real number tends to G(d₂) − G(d₁) < ε.toReal, so μ_{φ(j)}([s − δ, s]) ≤ ε for all large j.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n -i "helly|cmc_fc_gs|no_concentration|quotient_finite" local-references/123e8435b4a2469b/project --glob '*.lean' (no match)`
- `rg -n -i "helly" local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean' (only the convexity Helly theorem in Analysis/Convex/Radon.lean)`
- `rg -n -i "selection theorem|helly.?s selection|tendsto_subseq_of_bounded|exists_tendsto_subseq" local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `rg -n "theorem Monotone.countable_not_continuousAt|theorem IsCompact.tendsto_subseq |theorem isCompact_univ_pi|theorem measurable_measure_prodMk_left |theorem prod_apply_symm|theorem lintegral_liminf_le |theorem ae_lt_top |to_dual liminf_le_liminf_comp|to_dual frequently_lt_of_liminf_lt|theorem extraction_of_frequently_atTop |theorem _root_.Set.Countable.ae_notMem|theorem ae_restrict_neBot|theorem measure_sdiff |theorem Measurable.liminf " local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `rg -n "theorem Monotone.ae_differentiableAt|StieltjesFunction.measure_Ioc" local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `python3 scan of dag.json lean_name values (cmc_fc_*, *slice*, helly, fatou, concentr) and statements of lcmp_exists_good_slice_level, cmcs_slice_mass_integral, cmc_slice_mass_bounds`
- `sed -n 2760,2860p runtime.py (_install_speculative_assumptions stub scope); sed -n 540,615p verifier/gmt-compare.py (contract_scope/child_modules challenge scope); grep _existing_lean_name_problem runtime.py`
- `lake env lean /tmp/gsdec-ba6/{Types,Avail,Assembly,ProofA,ProofB}.lean and /tmp/gsdec-ba6/final/{ChallengeA,ChallengeB,Full}.lean (#check/#synth probes, elaboration, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convex/Radon.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-good-slice-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/tmp/gsdec-ba6/Types.lean`
- `/tmp/gsdec-ba6/Avail.lean`
- `/tmp/gsdec-ba6/Assembly.lean`
- `/tmp/gsdec-ba6/ProofA.lean`
- `/tmp/gsdec-ba6/ProofB.lean`
- `/tmp/gsdec-ba6/final/ChallengeA.lean`
- `/tmp/gsdec-ba6/final/ChallengeB.lean`
- `/tmp/gsdec-ba6/final/Full.lean`

Snapshot: project b4d606db, mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Neither the project, SimonGMT nor the pinned Mathlib contains a Helly-type selection theorem for distribution functions. The only Mathlib 'Helly' is the convexity theorem in Analysis/Convex/Radon.lean, and the snapshot has no no-concentration lemma. Nor does it have an a.e. bound on liminfs over j of difference quotients: Monotone.ae_differentiableAt (Analysis/Calculus/Monotone.lean:209) treats one monotone function, not a liminf over j. So both children are new obligations. Every tool the child proofs cite exists at the pinned paths, and #check confirms each after import GMT.Ch07.Submission:
- isCompact_univ_pi (Topology/Compactness/Compact.lean:1172)
- IsCompact.tendsto_subseq (Topology/Sequences.lean:298)
- tendsto_pi_nhds
- Monotone.countable_not_continuousAt (Topology/Order/Monotone.lean:166)
- exists_rat_btwn
- measure_sdiff (MeasureTheory/Measure/Basic.lean:215)
- measurable_measure_prodMk_left (Measure/Prod.lean:97)
- Measure.prod_apply and prod_apply_symm (Prod.lean:223 and 706)
- Real.volume_Ioo
- lintegral_const_mul
- Measurable.liminf (BorelSpace/Order.lean:1058)
- lintegral_liminf_le (Integral/Lebesgue/Add.lean:233)
- ae_lt_top (Lebesgue/Markov.lean:159)
- Filter.Tendsto.liminf_le_liminf_comp (Order/LiminfLimsup.lean:181, via to_dual)
- Filter.liminf_congr
- tendsto_one_div_add_atTop_nhds_zero_nat
The parent assembly uses Set.Countable.ae_notMem (NullSingletonClass.lean:63), ae_restrict_neBot (Restrict.lean:710), frequently_lt_of_liminf_lt and extraction_of_frequently_atTop. The instances FirstCountableTopology ({q : ℚ // ↑q ∈ Ioo a b} → ℝ) and NullSingletonClass (volume : Measure ℝ) synthesize. dag.json reserves no cmc_fc_gs_* name, so the two proposed names are fresh, and no accepted declaration has these types. Related nodes in other branches (lcmp_exists_good_slice_level, cmcs_slice_mass_integral) have different, unaccepted types and are not reused. Both child types elaborate in the comparator and speculative-stub scopes. The exact-type parent assembly and complete scratch proofs of both children compile with only propext, Classical.choice and Quot.sound.
