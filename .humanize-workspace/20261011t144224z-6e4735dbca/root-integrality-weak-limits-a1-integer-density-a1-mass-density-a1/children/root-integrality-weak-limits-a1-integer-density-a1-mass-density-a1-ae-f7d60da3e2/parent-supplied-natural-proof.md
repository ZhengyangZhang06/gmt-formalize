# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.ae_ball_growth-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 4 and (5a) of the parent proof of ind_mass_density_bound: Simon Ch. 1, Theorem 3.3 with t = ∞, followed by unpacking the finite upper density.

Conventions. ℝ^P := Eucl P and Hⁿ := μHE[n]. ω_n := realUnitBallVolume n = ENNReal.ofReal(π^{n/2}/Γ(n/2 + 1)) (realUnitBallVolume_eq). For x ∈ ℝ^P and r ∈ ℝ, q_x(r) := dimensionalDensityQuotient ν.toOuterMeasure n univ x r = ν(univ ∩ B̄_r(x)) / (ω_n · ENNReal.ofReal(r)^(n:ℝ)). Θ(x) := dimensionalUpperDensity ν.toOuterMeasure n univ x = limsup_{r→0+} q_x(r), the limsup along 𝓝[>] 0, a value in [0, ∞].

1. The infinite-density set is Hⁿ-null. Let A := {x ∈ ℝ^P : Θ(x) = ∞}. Apply the comparator-accepted declaration Submission.rectifiability_density_comparison with P, n, ν, A, V := univ (open) and t := ∞. Its hypotheses hold because A ⊆ univ and ∞ ≤ Θ(x) for every x ∈ A. It gives ∞ · Hⁿ(A) ≤ ν(ℝ^P) < ∞. If Hⁿ(A) ≠ 0, then ∞ · Hⁿ(A) = ∞ (ENNReal.top_mul), contradicting ν(ℝ^P) < ∞. Hence Hⁿ(A) = 0. The comparison theorem allows arbitrary, possibly non-measurable, A, and Hⁿ(A) is the outer measure.

2. Almost-everywhere finiteness. By ae_iff, '∀ᵐ x ∂Hⁿ, Θ(x) < ∞' means Hⁿ({x : ¬ Θ(x) < ∞}) = 0. That set is {x : Θ(x) = ∞} = A (not_lt, top_le_iff). By step 1, Θ(x) < ∞ for Hⁿ-a.e. x. It remains to prove the conclusion for each fixed x with Θ(x) < ∞.

3. Small radii. Fix x with Θ(x) < ∞ and put b := Θ(x) + 1. Then b < ∞ (ENNReal.add_ne_top) and Θ(x) < b (ENNReal.lt_add_right). Since limsup_{r→0+} q_x(r) = Θ(x) < b, eventually in 𝓝[>] 0 we have q_x(r) < b (eventually_lt_of_limsup_lt; the boundedness side condition is automatic in the complete lattice [0, ∞]). By mem_nhdsGT_iff_exists_Ioo_subset there is r₀ > 0 with q_x(r) < b for every r ∈ (0, r₀).

4. The constant ω_n. π^{n/2} > 0 (Real.rpow_pos_of_pos, Real.pi_pos) and Γ(n/2 + 1) > 0 (Real.Gamma_pos_of_pos). So π^{n/2}/Γ(n/2 + 1) > 0 and ω_n ≠ 0 (ENNReal.ofReal_eq_zero). Also ω_n ≠ ∞ because ofReal is finite.

5. Let r ∈ (0, r₀) and d := ω_n · ENNReal.ofReal(r)^(n:ℝ). Since n is a natural number and r ≥ 0, ENNReal.ofReal(r)^(n:ℝ) = ENNReal.ofReal(r)^n = ENNReal.ofReal(rⁿ) (ENNReal.rpow_natCast, ENNReal.ofReal_pow). As rⁿ > 0, ENNReal.ofReal(rⁿ) ∈ (0, ∞), so d ≠ 0 and d ≠ ∞. Moreover ν.toOuterMeasure(univ ∩ B̄_r(x)) = ν(B̄_r(x)) (univ_inter, Measure.coe_toOuterMeasure). So q_x(r) = ν(B̄_r(x))/d < b, and ENNReal.div_lt_iff (with d ≠ 0 and d ≠ ∞) gives ν(B̄_r(x)) < b · d.

6. Real constant. Put C := b.toReal · ω_n.toReal ∈ ℝ. Since b and ω_n are finite, b = ENNReal.ofReal(b.toReal) and ω_n = ENNReal.ofReal(ω_n.toReal) (ENNReal.ofReal_toReal). All real factors are nonnegative, so ENNReal.ofReal_mul gives
 b · d = ENNReal.ofReal(b.toReal) · (ENNReal.ofReal(ω_n.toReal) · ENNReal.ofReal(rⁿ)) = ENNReal.ofReal(b.toReal · (ω_n.toReal · rⁿ)) = ENNReal.ofReal(C · rⁿ).
 Hence ν(B̄_r(x)) < ENNReal.ofReal(C · rⁿ) for every r ∈ (0, r₀).

7. By step 2, the set of x where steps 3–6 apply has Hⁿ-null complement. So for Hⁿ-a.e. x there are C ∈ ℝ and r₀ > 0 as required. ∎

Implementation remark. A Lean proof of exactly this argument, taking the frozen type of rectifiability_density_comparison as a hypothesis, was compiled against the frozen project using only the axioms propext, Classical.choice and Quot.sound.

## Key steps

1. rectifiability_density_comparison with V = univ, t = ∞ and A = {Θ*ⁿ(ν,·) = ∞} gives ∞·Hⁿ(A) ≤ ν(ℝ^P) < ∞, so Hⁿ(A) = 0.
2. Hence Θ*ⁿ(ν, x) < ∞ for Hⁿ-a.e. x (ae_iff).
3. For such x, limsup_{r→0+} q_x(r) < Θ + 1 gives r₀ > 0 with q_x(r) < Θ + 1 on (0, r₀) (eventually_lt_of_limsup_lt, mem_nhdsGT_iff_exists_Ioo_subset).
4. ω_n·ofReal(r)^n ∈ (0, ∞), so ν(B̄_r(x)) < (Θ+1)·ω_n·ofReal(rⁿ) = ofReal(C rⁿ) with C = (Θ+1).toReal·ω_n.toReal.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/{Contract,Submission}.lean against workspace GMT/Ch06/{Contract,Submission}.lean (identical); cmp snapshot mathlib Portmanteau/HasOuterApproxClosed/Embedding/Comap/Sequences/LiminfLimsup/Geometry/Euclidean/Volume/Measure.lean against .lake copies (identical)`
- `python3 scan of dag.json: lean_name/status/lean_statement of all 360 nodes; ind_* names; frozen types of iwl_restriction_theory, rectifiability_density_comparison, rectifiability_mass_measure_representation (all accepted); statements containing dimensionalUpperDensity|IsMassMeasure|closedBall x r|limsup (fun`
- `git grep 'ind_md_' over all refs; grep -rn 'ind_md_|closedBall_weak_subseq|diagonal_weak_subseq|ae_closedBall_growth|mass_measure_balls' snapshot project + mathlib/Mathlib + simongmt (no match)`
- `git show afac113:GMT/Ch06/Submission.lean | grep 'theorem Submission.|import|namespace' (Submission.X declared inside namespace GMT.Ch06; accepted versions add SimonGMT imports)`
- `grep -n 'def massOn|def mass|massOn_mono|le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `grep -n 'finiteMeasure_tendsto_subseq_of_compact_metrizable|simon_theorem_4_16_compact_metrizable|def dimensionalUpperDensity|def dimensionalDensityQuotient|def realUnitBallVolume' simongmt/Poincare/SimonGMT/Chapter01/*.lean`
- `grep -rn 'limsup_measure_closed_le_of_tendsto|class HasOuterApproxClosed|instance|notation "μHE\["|theorem comap_apply|theorem subtype_coe|IsCompact.tendsto_subseq|limsup_eq_iInf_iSup_of_nat' mathlib/Mathlib`
- `python3 -I: gmt-compare.contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') and lean_contract.validate_lean_statement on the 4 child statements and the parent`
- `lake env lean /tmp/mdb-decomp/{Stmts,Api,Assembly,Feas1,Feas2,Feas3,Feas4,Final,Final2}.lean with #print axioms`
- `sed -n 2400,2445p book/chapter-06.txt (printed Proof of 8.2, display (8)); grep -n '3.3 Theorem|4.16 Theorem' book/chapter-01.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Comap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/mdb-decomp/Stmts.lean`
- `/tmp/mdb-decomp/Assembly.lean`
- `/tmp/mdb-decomp/Final.lean`
- `/tmp/mdb-decomp/Final2.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract and a byte-identical Submission. Both are identical to the workspace copies compiled against.

The supplied proof is fully supported by local declarations:
- SimonGMT GeometricCurrentOn.mass = massOn univ and massOn_mono (Chapter06/Mass.lean).
- finiteMeasure_tendsto_subseq_of_compact_metrizable (Chapter01/CompactMetrizableCompactness.lean; normalizes masses, so no metrizability of FiniteMeasure is needed).
- dimensionalUpperDensity / dimensionalDensityQuotient (Chapter01/Densities.lean) and realUnitBallVolume (Chapter01/Hausdorff.lean).
- Mathlib FiniteMeasure.limsup_measure_closed_le_of_tendsto, with HasOuterApproxClosed for pseudo-metrizable spaces.
- MeasurableEmbedding.subtype_coe and comap_apply, Monotone.measure_iUnion, iUnion_ball_nat, limsup_eq_iInf_iSup_of_nat, eventually_lt_of_limsup_lt, mem_nhdsGT_iff_exists_Ioo_subset, and the μHE notation.

The accepted DAG declarations iwl_restriction_theory (R2) and rectifiability_density_comparison are reused with byte-identical frozen types. No ind_md_* name exists anywhere.

Scratch Lean checks (/tmp/mdb-decomp):
- All 4 child statements elaborate in the comparator's contract scope, and `exact Submission.<name>` resolves for each.
- parent_of_children proves the exact frozen parent type from children 1, 3 and 4, and diag_of_single proves child 3 from child 2.
- Complete proofs of children 1, 2 and 4 compile.
- Every check uses only the axioms propext, Classical.choice and Quot.sound.

The printed Proof of 8.2 (chapter-06.txt lines 2420–2435) asserts that (8) remains valid for T_{j′} without proof; the supplied corrected argument fills this gap. Simon Ch. 1 3.3 and 4.16 are at chapter-01.txt lines 602 and 1750.
