# Parent-supplied natural-language proof

- Parent DAG node: `root.sobolev_inequality-a1`
- Child DAG node: `root.sobolev_inequality-a1.good_radius_calculus-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. All functions are real valued on ℝ; ∫_{(a,b]} and ∫_a^b denote Lebesgue integrals over (a, b] and [a, b] (equal, and equal to the integral over (a, b), for integrable functions). Source: Step 2 of the parent proof, the corrected Lemma 5.8 of Simon Ch. 4. Documented correction: Simon's printed Lemma 5.8 is inconsistent (its lower bound 1 ≤ σ^{−n}f(σ) for all σ contradicts boundedness of f); it is replaced by this version (lower bound only along small radii, i.e. limsup_{s↓0} s^{−n}f(s) ≥ 1, finite-interval inequality, same good-radius conclusion), and n ≥ 2 is required. Here F is any upper bound of f on (0, ∞); the parent proof takes F = f_∞ = sup f, and its argument uses only f ≤ F and r_0^{−n}F = 2^{−n}.

1. (F > 0.) Apply (b) with η = 0: since the frequently-condition is non-vacuous, there is s > 0 with f(s)/sⁿ > 0, so F ≥ f(s) > 0.
2. Put r_0 := 2F^{1/n} > 0. Since F > 0, (F^{1/n})ⁿ = F (Mathlib Real.rpow_inv_natCast_pow), so r_0ⁿ = 2ⁿF, i.e. r_0^{−n}F = 2^{−n}, and 5ⁿF^{1/n} = ½·5ⁿr_0.
3. (Integrability.) For 0 < a ≤ b, a function that is nondecreasing on [a, b] is measurable and bounded there (between its values at a and b), and τ ↦ τ^{−n} is continuous on [a, b]. Hence τ ↦ τ^{−n}k(τ), τ ↦ τ^{−n}f(τ) and τ ↦ τ^{−n}f(5τ) (f(5·) is nondecreasing on (0, ∞)) are integrable on [a, b] (Mathlib MonotoneOn.intervalIntegrable; for τ^{−n}k(τ) this is also SimonGMT Chapter04.intervalIntegrable_radiusQuotient_of_monotoneOn, axiom-clean). All integrals below are of such functions.
4. Suppose, for a contradiction, that the conclusion fails: for every r with 0 < r < r_0, f(5r) > 5ⁿF^{1/n}k(r) = ½·5ⁿr_0k(r), i.e. k(r) < (2/(5ⁿr_0))·f(5r).
5. By (b) with η = 2/3, and since (0, r_0) belongs to the filter 𝓝[>]0, there is s with 0 < s < r_0 and f(s)/sⁿ > 2/3.
6. Let S := sup{τ^{−n}f(τ) : τ ∈ [s, r_0]}. The set is nonempty and bounded above by s^{−n}F (because f ≤ F, F > 0 and τⁿ ≥ sⁿ), so S is a real number; S ≥ s^{−n}f(s) > 2/3, and S ≥ 0.
7. Fix s' ∈ [s, r_0]. Hypothesis (a) with the pair (s', r_0) and f(r_0) ≤ F give s'^{−n}f(s') ≤ r_0^{−n}F + ∫_{(s',r_0]} τ^{−n}k(τ) dτ = 2^{−n} + ∫_{s'}^{r_0} τ^{−n}k(τ) dτ.
8. By step 4, τ^{−n}k(τ) ≤ (2/(5ⁿr_0))·τ^{−n}f(5τ) for all τ ∈ [s', r_0) (the endpoint r_0 is a null set), so by step 3, ∫_{s'}^{r_0} τ^{−n}k(τ) dτ ≤ (2/(5ⁿr_0))∫_{s'}^{r_0} τ^{−n}f(5τ) dτ.
9. Substituting u = 5τ (τ^{−n} = 5ⁿu^{−n}, dτ = du/5; Mathlib intervalIntegral.integral_comp_mul_left): ∫_{s'}^{r_0} τ^{−n}f(5τ) dτ = 5^{n−1}∫_{5s'}^{5r_0} u^{−n}f(u) du. Hence the bound of step 8 equals (2/(5r_0))∫_{5s'}^{5r_0} u^{−n}f(u) du.
10. As s ≤ s' ≤ 5s' and u^{−n}f(u) ≥ 0 for u > 0, ∫_{5s'}^{5r_0} u^{−n}f(u) du ≤ ∫_s^{r_0} u^{−n}f(u) du + ∫_{r_0}^{5r_0} u^{−n}f(u) du. The first integral is ≤ (r_0 − s)S ≤ r_0S (its integrand is ≤ S on [s, r_0] and S ≥ 0). In the second, f(u) ≤ F, so it is ≤ F∫_{r_0}^{5r_0} u^{−n} du = F(r_0^{1−n} − (5r_0)^{1−n})/(n − 1) ≤ F r_0^{1−n}/(n − 1) ≤ F r_0^{1−n}, using n ≥ 2.
11. Combining steps 7–10: s'^{−n}f(s') ≤ 2^{−n} + (2/(5r_0))(r_0S + F r_0^{1−n}) = 2^{−n} + (2/5)S + (2/5)F r_0^{−n} = (7/5)2^{−n} + (2/5)S.
12. Step 11 holds for every s' ∈ [s, r_0]; taking the supremum, S ≤ (7/5)2^{−n} + (2/5)S, so (3/5)S ≤ (7/5)2^{−n}, i.e. S ≤ (7/3)2^{−n} ≤ (7/3)(1/4) = 7/12 because n ≥ 2.
13. This contradicts S > 2/3 (step 6). Therefore the assumption of step 4 is false: there is r with 0 < r < r_0 = 2F^{1/n} and f(5r) ≤ 5ⁿF^{1/n}k(r). Together with step 1 (0 < F) this is the claim. ∎

## Key steps

1. F > 0 from (b); r_0 := 2F^{1/n} satisfies r_0^{−n}F = 2^{−n}
2. Assume k(r) < 2·5^{−n}r_0^{−1}f(5r) on (0, r_0) and pick s ∈ (0, r_0) with s^{−n}f(s) > 2/3
3. With S = sup_{[s,r_0]} τ^{−n}f(τ) < ∞, (a) at (s', r_0) and the substitution u = 5τ give s'^{−n}f(s') ≤ 2^{−n} + (2/(5r_0))∫_{5s'}^{5r_0}u^{−n}f(u)du
4. Split [5s', 5r_0] ⊆ [s, r_0] ∪ [r_0, 5r_0] to get S ≤ (7/5)2^{−n} + (2/5)S, so S ≤ 7/12 < 2/3, a contradiction

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n 'theorem exists_disjoint_subfamily_covering_enlargement_closedBall' -A 12 <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n 'theorem lintegral_comp_eq_lintegral_meas_lt_mul|theorem lintegral_eq_lintegral_meas_lt|theorem lintegral_comp_eq_lintegral_meas_le_mul|theorem lintegral_rpow_eq_lintegral_meas_lt_mul' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `rg -n 'countable_of_nonempty_interior|countable_of_isOpen' <snapshot>/mathlib/Mathlib`
- `rg -n '^theorem|^lemma|^def|^protected theorem' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `sed -n 586,880p book/chapter-04.txt (Simon 5.1-5.9 printed text)`
- `grep -rn 'theorem contDiff_of_tsupport_subset|theorem exists_fiveTimesCovering|theorem integrableOn_norm_tangentialGradient' lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `cat simongmt/Poincare/SimonGMT/Chapter04/{SobolevCovering,GoodRadius,SobolevGoodRadius,SobolevTruncation,SobolevLayerCake,Sobolev,CompactWeighted}.lean Chapter01/DensityCovering.lean`
- `git -C lake-packages-25730c7c/simongmt rev-parse HEAD`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/sobolev-a1-audit/olean/GMT/Ch04/Submission.olean`
- `python3 -I gen_challenges.py: verifier/lean_contract.validate_lean_statement + gmt-compare.child_modules(mode=contract) for each child; LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/sobolev-a1-audit/olean lean Challenge_<name>.lean`
- `LEAN_PATH=... lean /tmp/sobolev-a1-audit/lean/Assembly.lean (parent frozen type proved from the uncle and six sorry'd children; #print axioms)`
- `LEAN_PATH=... lean /tmp/sobolev-a1-audit/lean/Inspect.lean (Iff.rfl against explicit @HPow.hPow ℝ ℕ ℝ / Real.rpow / Measure toReal forms)`
- `lake env lean /tmp/sobolev-a1-audit/lean/Axioms.lean (#print axioms of cited SimonGMT and Mathlib lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-sobolev-inequality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/SobolevCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/GoodRadius.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/SobolevGoodRadius.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/SobolevTruncation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/SobolevLayerCake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Sobolev.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/CompactWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/sobolev-a1-audit/children.json`
- `/tmp/sobolev-a1-audit/lean/Assembly.lean`
- `/tmp/sobolev-a1-audit/lean/Inspect.lean`
- `/tmp/sobolev-a1-audit/lean/Axioms.lean`

Contract provenance. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 6e58e5dd…0f4770b). The manifest pins project ff75f52 and Mathlib 25730c7c. The SimonGMT package is at the pinned revision 2b3663083f3fe399b6296fb8eaee52169170e197.

Mathlib lemmas available in the snapshot, each depending only on propext, Classical.choice and Quot.sound:
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (requires τ > 3; used with τ = 5)
- Set.PairwiseDisjoint.countable_of_nonempty_interior
- the Layercake lemmas lintegral_comp_eq_lintegral_meas_lt_mul and lintegral_rpow_eq_lintegral_meas_lt_mul
- Real.smoothTransition (smooth, monotone, values in [0,1], 0 on (−∞,0], 1 on [1,∞))
- withDensity_absolutelyContinuous, exists_measurable_superset_of_null, Tendsto.limUnder_eq
- LocallyIntegrableOn.integrableOn_compact_subset, Continuous.integrable_of_hasCompactSupport
- intervalIntegral.integral_comp_mul_left, MonotoneOn.intervalIntegrable, Real.rpow_inv_natCast_pow
- Submodule.norm_starProjection_apply_le

Pinned SimonGMT. It contains a kernel-checked Sobolev proof for its own Chapter04.RectifiableVarifold. That structure differs from the contract's, so its varifold-specific lemmas cannot be applied. Its general lemmas are reusable as tools, each with the same three axioms only:
- Chapter04.lintegral_le_of_ae_exists_good_radius (5-times covering plus summation)
- exists_smooth_superlevel_cutoff
- lintegral_smooth_truncation_energy_le
- lintegral_superlevel_le_of_positive_shifts
- rpow_one_sub_le_of_le_rpow_mul
- intervalIntegrable_radiusQuotient_of_monotoneOn
- RectifiableVarifold.contDiff_of_tsupport_subset (fully general despite the namespace)
- Chapter01.exists_fiveTimesCovering
Its calculus lemma exists_goodRadius_of_local_radius_inequality has a weaker constant (4·5ⁿM^{1/n}, r ≤ R). The corrected Lemma 5.8 child therefore keeps the parent's sharp constant and is proved directly.

Child type checks. With GMT.Ch04.Submission compiled to an olean:
- All six child types pass validate_lean_statement and elaborate in comparator-generated NodeChallenge files (contract scope: the opens, namespace GMT.Ch04, noncomputable section, open RectifiableVarifold); the only diagnostics are the expected sorry warnings.
- Iff.rfl confirms ℕ-powers and Real.rpow where intended.
- The parent's frozen type is proved, with no sorry in its body, from the uncle weighted_monotonicity_identity (frozen type copied byte-identically) and the six children. #print axioms shows sorryAx only through the stubs.
