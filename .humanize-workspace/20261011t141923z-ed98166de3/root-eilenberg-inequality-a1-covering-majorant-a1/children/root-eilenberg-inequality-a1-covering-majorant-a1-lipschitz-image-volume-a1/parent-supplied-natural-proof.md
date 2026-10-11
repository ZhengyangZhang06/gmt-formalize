# Parent-supplied natural-language proof

- Parent DAG node: `root.eilenberg_inequality-a1.covering_majorant-a1`
- Child DAG node: `root.eilenberg_inequality-a1.covering_majorant-a1.lipschitz_image_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the isodiametric step of the printed proof of Simon, Introduction to GMT, Ch. 2, Theorem 1.9 (p. 46): 'where we used Lᵐ(f(C_ij)) ≤ ω_m (diam f(C_ij)/2)^m (by the isodiametric inequality 2.10) ≤ ω_m (Lip f)^m (diam C_ij/2)^m'.

It carries the parent proof's documented correction (a): f(C_ij) need not be Borel, so the closed set closure f(D) is measured instead. That set has the same diameter as f(D); in the parent, D = C_ij ∩ E. This is parent step 5 together with the first half of parent step 8.

The isodiametric inequality 2.10 is the kernel-checked SimonGMT theorem `Poincare.SimonGMT.Chapter01.simon_theorem_2_10 (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) : volume A ≤ realUnitBallVolume (n : ℝ) * (ediam A / 2) ^ (n : ℝ)`. It is valid for every n ∈ ℕ, including n = 0, and every set A, with no measurability assumption.

It lives in module `Poincare.SimonGMT.Chapter01.EuclideanNormalization`, which the frozen contract does not import. Add `import Poincare.SimonGMT.Chapter01.EuclideanNormalization` to GMT/Ch02/Submission.lean. The verifier does not byte-check Submission.lean, and this import was checked to compile together with the existing imports. No other erratum.

Conventions. ediam is Mathlib's extended diameter `Metric.ediam` (values in [0,∞], ediam ∅ = 0). `LipschitzOnWith K f D` means edist (f x) (f x') ≤ K·edist x x' for all x, x' ∈ D; apply it directly as `hf hx hx'`. ω_m := Chapter01.realUnitBallVolume m. All arithmetic is in ℝ≥0∞, and K^m, (ediam D)^m and 2^m are natural powers.

Proof.
1. (Diameter of the image.) Put d := ediam D. Let x, x' ∈ D. The Lipschitz hypothesis gives edist (f x) (f x') ≤ K·edist x x'. Since edist x x' ≤ ediam D (`Metric.edist_le_ediam_of_mem`) and multiplication by K is monotone on [0,∞], edist (f x) (f x') ≤ K·d. In Lean use `gcongr`; `mul_le_mul_left'` is not available in this Mathlib. Every pair of points of f(D) has the form (f x, f x') with x, x' ∈ D, so ediam (f(D)) ≤ K·d (`Metric.ediam_le`, after `rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩`).
2. (Closure.) The closure has the same extended diameter: ediam (closure (f(D))) = ediam (f(D)) (`Metric.ediam_closure`).
3. (Isodiametric inequality.) Apply simon_theorem_2_10 with n = m and A = closure (f(D)) ⊆ ℝᵐ. This gives Lᵐ(closure f(D)) ≤ ω_m·(ediam (closure f(D))/2)^(m:ℝ), which equals ω_m·(ediam (f(D))/2)^m by step 2 and `ENNReal.rpow_natCast` (x^(m:ℝ) = x^m).
4. (Monotonicity.) The map x ↦ ω_m·(x/2)^m is monotone on [0,∞], because division by the constant 2 and natural powers are monotone (`gcongr`). By step 1, ω_m·(ediam (f(D))/2)^m ≤ ω_m·(K·d/2)^m.
5. (Algebra in [0,∞].) Write x/y = x·y⁻¹ (`div_eq_mul_inv`). Then (K·d·2⁻¹)^m = K^m·d^m·(2⁻¹)^m = K^m·d^m·(2^m)⁻¹ (`mul_pow`, `ENNReal.inv_pow`). By commutativity and associativity (`ring`), ω_m·(K·d/2)^m = ω_m·K^m·d^m/2^m. No cancellation is used, so this identity holds for all values, including d = ∞, K = 0 and m = 0.
6. (Conclusion.) Chaining steps 3, 4 and 5 gives Lᵐ(closure (f(D))) ≤ ω_m·K^m·(ediam D)^m/2^m. ∎

## Key steps

1. From the Lipschitz condition and edist ≤ ediam: ediam f(D) ≤ K·ediam D (Metric.ediam_le, Metric.edist_le_ediam_of_mem).
2. ediam (closure f(D)) = ediam f(D) (Metric.ediam_closure).
3. Isodiametric inequality simon_theorem_2_10 with n = m for A = closure f(D), converting the exponent (m:ℝ) to the natural power m (ENNReal.rpow_natCast).
4. Monotonicity of x ↦ ω_m (x/2)^m and the ENNReal identity ω_m (K d/2)^m = ω_m K^m d^m / 2^m (div_eq_mul_inv, mul_pow, ENNReal.inv_pow, ring).

## Reference use

### local-project

Queries:
- `cat local-references/ff09f3909baeeae7/manifest.json (mode local-project, project 1b1689a8deba89d58b36b1a04dba493693824437, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/ff09f3909baeeae7/project/GMT/Ch02/{Contract,Submission}.lean against workspace GMT/Ch02/{Contract,Submission}.lean (identical)`
- `sed -n 530,600p mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean (hausdorffMeasure_apply, hausdorffMeasure_le_liminf_tsum)`
- `grep -n 'def ediam|theorem ediam_closure|theorem ediam_le|theorem ediam_mono|theorem ediam_empty|theorem ediam_image_le' -r mathlib/Mathlib/Topology; sed -n 1,60p mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `grep -rn -E 'theorem lintegral_liminf_le|theorem Measurable.liminf|theorem lintegral_tsum|theorem lintegral_indicator_const|theorem Measurable.ennreal_tsum|theorem rpow_add_of_nonneg|theorem rpow_add|theorem rpow_natCast|theorem tendsto_inv_nat_nhds_zero|theorem Tendsto.const_mul|theorem tsum_mul_left|theorem lintegral_const_mul|theorem Measurable.indicator|theorem lt_add_right|theorem mul_rpow_of_nonneg|theorem div_rpow_of_nonneg|theorem rpow_le_rpow|theorem zero_rpow_of_pos' mathlib/Mathlib`
- `grep -rn -E '(theorem|lemma) .*(Tendsto.liminf_eq|mul_iSup|le_liminf_of_le|liminf_le_liminf|iInf_lt_iff|div_pow|tsum_le_tsum)' mathlib/Mathlib`
- `grep -n 'def simonHausdorffMeasureReal|def realUnitBallVolume|theorem realUnitBallVolume_pos|theorem realUnitBallVolume_ne_top' -A6 lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `sed -n 1,60p lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/EuclideanNormalization.lean (simon_theorem_2_10)`
- `rg -n -i 'eilenberg|covering_majorant|liminf_majorant|fixed_scale' local-references/ff09f3909baeeae7/project; rg -n -i 'eilenberg' lake-packages-25730c7c/simongmt/Poincare/SimonGMT; rg -n -i 'theorem .*(lipschitz.*volume|volume.*lipschitz|image_volume)' mathlib/Mathlib lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `find lake-packages-25730c7c/simongmt -name 'UpperIntegral*'; rg -n 'exists_measurableMajorant|upperLebesgueIntegral' lake-packages-25730c7c/simongmt/Poincare`
- `lean checks/Names.lean: #check of 54 API names (hausdorffMeasure_apply, Metric.ediam_*, simon_theorem_2_10, lintegral_liminf_le, Measurable.liminf, ENNReal.rpow_add(_of_nonneg), Filter.Tendsto.liminf_eq, ENNReal.mul_iSup, iInf_lt_iff, ...) against a scratch olean of GMT.Ch02.Submission built with plain lean -o (no lake build)`
- `python3 -I scripts/gen_challenge.py (imports verifier/gmt-compare.py child_modules/contract_scope and lean_contract.validate_lean_statement) then lean checks/final/NodeChallenge_00..02.lean`
- `lean checks/AssemblyCheck2.lean (parent frozen type from the child types as hypotheses) + #print axioms`
- `lean checks/ChildA.lean, checks/ChildC.lean (outright proofs), checks/ChildB.lean (B from A), checks/FullCheck.lean; lean -o of sim/GMT/Ch02/Submission.lean containing the children, then lean simsol/NodeSolution_00..03.lean + #print axioms`
- `python3 -I: collect all lean_name values in dag.json and nodes/*/*.json`
- `sed -n 240,600p verifier/gmt-compare.py (candidate_inputs/frozen_inputs: Submission.lean not byte-checked; new Lean files allowed only under GMT/Ch02/)`
- `grep -n '1.9|Eilenberg|isodiametric' book/chapter-02.txt; sed -n 330,425p book/chapter-02.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/EuclideanNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-eilenberg-inequality-a1-covering-majorant-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/covmaj-decomp-jd8mrR/checks/Names.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/final/NodeChallenge_00.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/final/NodeChallenge_01.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/final/NodeChallenge_02.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/AssemblyCheck2.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/ChildA.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/ChildB.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/ChildC.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/FullCheck.lean`
- `/tmp/covmaj-decomp-jd8mrR/sim/GMT/Ch02/Submission.lean`
- `/tmp/covmaj-decomp-jd8mrR/simsol/NodeSolution_00.lean`
- `/tmp/covmaj-decomp-jd8mrR/simsol/NodeSolution_01.lean`
- `/tmp/covmaj-decomp-jd8mrR/simsol/NodeSolution_02.lean`
- `/tmp/covmaj-decomp-jd8mrR/simsol/NodeSolution_03.lean`

**No existing result.**
- The snapshot project (identical to the workspace Contract/Submission) contains only the frozen definition EilenbergInequality (Contract.lean:232) and README row 6.
- SimonGMT has no Eilenberg, covering-majorant or fixed-scale lemma.
- No Lipschitz-image Lebesgue-volume lemma exists; the only lipschitz/volume matches are area-formula results in Chapter02/AreaLiteral.lean.
- Chapter02/UpperIntegral.lean (upperLebesgueIntegral) is not needed, because correction (b) uses an explicit liminf majorant.

**Mathlib API, all #check-ed in the pinned environment.**
- Hausdorff measure: Measure.hausdorffMeasure_apply (Hausdorff.lean:546; covers with ediam ≤ r, Nonempty-weighted cost).
- Diameters: Metric.ediam_le, Metric.ediam_mono, Metric.edist_le_ediam_of_mem (EMetricSpace/Diam.lean); Metric.ediam_closure (Instances/ENNReal/Lemmas.lean:649).
- Lebesgue integral: lintegral_liminf_le (Lebesgue/Add.lean:233), lintegral_tsum (Add.lean:362), lintegral_indicator_const (Basic.lean:541).
- Measurability: Measurable.liminf (BorelSpace/Order.lean:1058); Measurable.ennreal_tsum (deprecated but available, BorelSpace/Real.lean:354).
- ENNReal powers: ENNReal.rpow_add_of_nonneg (Pow/NNReal.lean:633), ENNReal.rpow_add (:626), ENNReal.rpow_natCast (:686), ENNReal.inv_pow, ENNReal.mul_inv.
- ENNReal sums and limits: ENNReal.mul_iSup, ENNReal.tsum_mul_left, ENNReal.tsum_le_tsum, ENNReal.lt_add_right, ENNReal.tendsto_inv_nat_nhds_zero (ENNReal/Lemmas.lean:486), ENNReal.Tendsto.const_mul (:354).
- Order and filters: Filter.Tendsto.liminf_eq (Order/LiminfLimsup.lean:195), Filter.le_liminf_of_le, Filter.liminf_le_liminf, Filter.Tendsto.eventually_le_const, iInf_lt_iff, iInf₂_le_of_le.
- Not available in this Mathlib: ENNReal.div_pow, LipschitzOnWith.edist_le_mul, mul_le_mul_left' (use gcongr). A bare gcongr descends into the infimum, so use gcongr c * ?_.

**SimonGMT (pinned package).**
- simonHausdorffMeasureReal s = (realUnitBallVolume s / 2^s) • μH[s] (Chapter01/Hausdorff.lean:283).
- realUnitBallVolume_pos and realUnitBallVolume_ne_top (:499, :506).
- simon_theorem_2_10, the isodiametric inequality for every n and every set (EuclideanNormalization.lean:24), is not imported by the contract. Adding the import to Submission.lean is allowed: the verifier does not byte-check Submission.lean.

**Contract scope.** The comparator replays the bare `end` that closes the noncomputable section, so the 𝓗[·]/ω[·] local notations are unavailable. The child statements therefore spell out Chapter01.* and μH[·], with open MeasureTheory Metric Set Filter Topology, ENNReal, NNReal and Poincare.SimonGMT in scope.

**Lean verification.**
- All three child lean_statements elaborate in the replayed scope.
- The parent frozen type follows from the fixed-scale and liminf child types with axioms [propext, Classical.choice, Quot.sound].
- The isodiametric and liminf children were proved outright, and the fixed-scale child from the isodiametric one, with standard axioms.
- Comparator-style NodeSolution modules pass for all three children and the parent against a simulated Submission.

**Name collisions.** dag.json and the node files reserve only the existing depth-1/2 names (including eilenberg_compact_exhaustion, eilenberg_compact_fiber_measurable, eilenberg_covering_majorant, eilenberg_inequality_theorem); the three new eilenberg_covering_* names are free.
