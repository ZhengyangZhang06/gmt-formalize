# Parent-supplied natural-language proof

- Parent DAG node: `root.eilenberg_inequality-a1.covering_majorant-a1`
- Child DAG node: `root.eilenberg_inequality-a1.covering_majorant-a1.liminf_majorant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the limiting step of the printed proof of Simon, Introduction to GMT, Ch. 2, Theorem 1.9 (p. 46): 'Letting i → ∞ we conclude ∫* H^k(A ∩ f⁻¹y) dLᵐ(y) ≤ (ω_mω_k/ω_{m+k})(Lip f)^m H^{m+k}(A)'. It is taken in the completed form of the parent proof (its steps 9-11).

It carries the documented correction (b): instead of the upper integral ∫* of Remark 1.10, an explicit Borel majorant G := liminf_i g_i is built and Fatou's lemma is applied. The parent's specific data are generalized: the scales δ_i = 1/(i+1) become an arbitrary sequence r_i → 0, the constant c_k becomes c, and the bounds a(M + ε_i) → aM become b_i → L. No other erratum.

Conventions. ediam = Mathlib `Metric.ediam`. For ρ ∈ [0,∞] and S ⊆ X, pre^d_ρ(S) := ⨅ (t : ℕ → Set X) (_ : S ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ ρ), ∑' n, ⨆ (_ : (t n).Nonempty), ediam (t n) ^ d. This is the inner expression of Mathlib's `MeasureTheory.Measure.hausdorffMeasure_apply`: μH[d](S) = ⨆ (ρ : ℝ≥0∞) (_ : 0 < ρ), pre^d_ρ(S) for every S ⊆ X, with no measurability needed. All values lie in [0,∞], a complete linear order.

Proof.
1. (The majorant.) Define G(y) := liminf_{i→∞} g_i(y), i.e. `Filter.liminf (fun i ↦ g i y) atTop`. Since every g_i is measurable, G is measurable (`Measurable.liminf`; [0,∞] carries its Borel σ-algebra and a second-countable order topology).
2. (Monotonicity in the scale.) If ρ ≤ R, then pre^d_R(S) ≤ pre^d_ρ(S) for every S ⊆ X. Take any t with S ⊆ ⋃_n t_n and ediam t_n ≤ ρ for all n. Then also ediam t_n ≤ ρ ≤ R, so t is admissible at scale R and pre^d_R(S) ≤ Σ'_n [t_n ≠ ∅](ediam t_n)^d (`iInf₂_le_of_le` with t and the covering proof, then `iInf_le_of_le` with the diameter proof). Taking the infimum over all such t gives the claim (`le_iInf` three times).
3. (Domination at each positive scale.) Fix y ∈ Y and R ∈ [0,∞] with 0 < R. Since r_i → 0 and 0 < R, eventually r_i ≤ R (`Filter.Tendsto.eventually_le_const`). For every such i, step 2, monotonicity of multiplication by c, and the hypothesis give c·pre^d_R(F(y)) ≤ c·pre^d_{r_i}(F(y)) ≤ g_i(y). In Lean use `gcongr c * ?_`; a bare `gcongr` descends into the infimum. Hence c·pre^d_R(F(y)) ≤ liminf_i g_i(y) = G(y) (`Filter.le_liminf_of_le`). Its coboundedness side condition is automatic in the complete lattice [0,∞] (`isBoundedDefault`).
4. (Domination of the Hausdorff measure.) By `hausdorffMeasure_apply`, c·μH[d](F(y)) = c·⨆_R ⨆_{0<R} pre^d_R(F(y)) = ⨆_R ⨆_{0<R} c·pre^d_R(F(y)), applying `ENNReal.mul_iSup` twice. Each term is ≤ G(y) by step 3, so c·μH[d](F(y)) ≤ G(y) (`iSup_le` twice).
5. (Integral bound.) By Fatou's lemma (`MeasureTheory.lintegral_liminf_le`; all g_i are measurable and atTop on ℕ is countably generated), ∫⁻ G dν ≤ liminf_i ∫⁻ g_i dν. Since ∫⁻ g_i dν ≤ b_i for every i, liminf_i ∫⁻ g_i dν ≤ liminf_i b_i (`Filter.liminf_le_liminf` with `Filter.Eventually.of_forall`; the boundedness side conditions are automatic in [0,∞]). Since b_i → L and atTop is nontrivial, liminf_i b_i = L (`Filter.Tendsto.liminf_eq`). Hence ∫⁻ G dν ≤ L.
6. (Conclusion.) G is measurable (step 1), c·μH[d](F(y)) ≤ G(y) for every y (step 4), and ∫⁻ G dν ≤ L (step 5). ∎

## Key steps

1. G := liminf_i g_i is measurable (Measurable.liminf).
2. Covers admissible at scale r_i are admissible at any larger scale R, so pre^d_R ≤ pre^d_{r_i} once r_i ≤ R. Since r_i → 0, this holds eventually for every R > 0, giving c·pre^d_R(F y) ≤ g_i(y) eventually and hence c·pre^d_R(F y) ≤ G(y).
3. hausdorffMeasure_apply and ENNReal.mul_iSup turn the scale-wise bounds into c·μH[d](F y) ≤ G(y).
4. Fatou (lintegral_liminf_le), liminf monotonicity and Tendsto.liminf_eq give ∫ G dν ≤ liminf b_i = L.

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
