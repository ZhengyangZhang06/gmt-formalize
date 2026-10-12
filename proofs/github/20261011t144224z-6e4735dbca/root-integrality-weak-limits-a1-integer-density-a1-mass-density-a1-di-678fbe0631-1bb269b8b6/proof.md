# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.diagonal_weak_subseq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps (2b), (2c) and 3 of the parent proof of ind_mass_density_bound: nested subsequences over R = 0, 1, 2, … and the diagonal φ(j) = (χ_0∘⋯∘χ_j)(j). Here the portmanteau limsup inequality is carried along the diagonal instead of weak convergence. The inequality passes to subsequences, so this gives the same conclusion without re-deriving convergence.

Conventions. ℝ^P := Eucl P. Measures take values in [0, ∞]. limsup means Filter.limsup along atTop. Every strictly increasing χ : ℕ → ℕ satisfies χ(k) ≥ k for all k (StrictMono.id_le), and compositions of strictly increasing maps are strictly increasing (StrictMono.comp).

1. One extraction step. Let R ∈ ℕ and ψ : ℕ → ℕ be arbitrary. Each μ_{ψ(i)}(ℝ^P) is one of the μ_j(ℝ^P), so sup_i μ_{ψ(i)}(ℝ^P) ≤ sup_j μ_j(ℝ^P) < ∞ (iSup_le, le_iSup). Apply the sibling theorem Submission.ind_md_closedBall_weak_subseq to P, R and the sequence i ↦ μ_{ψ(i)}. It gives a strictly increasing χ_{R,ψ} : ℕ → ℕ and a measure ν_{R,ψ} with ν_{R,ψ}(ℝ^P) < ∞ and limsup_i μ_{ψ(χ_{R,ψ}(i))}(F) ≤ ν_{R,ψ}(F) for every closed F ⊆ B̄_R(0). By choice, fix such χ_{R,ψ} and ν_{R,ψ} for every pair (R, ψ) (Lean: choose).

2. Nested subsequences. Define p_R : ℕ → ℕ by recursion on R: p_0 := id and p_{R+1} := p_R ∘ χ_{R,p_R} (Lean: Nat.rec; both defining equations hold by rfl). By induction on R every p_R is strictly increasing: id is, and p_{R+1} is a composition of the strictly increasing maps p_R and χ_{R,p_R}. Put ν_R := ν_{R,p_R}. Step 1 for the pair (R, p_R) gives ν_R(ℝ^P) < ∞. Since p_R(χ_{R,p_R}(i)) = p_{R+1}(i), it also gives
 (∗) limsup_i μ_{p_{R+1}(i)}(F) ≤ ν_R(F) for every closed F ⊆ B̄_R(0).

3. Tails. For all R, d ∈ ℕ there is a strictly increasing g : ℕ → ℕ with p_{R+1+d} = p_{R+1} ∘ g. Proof by induction on d. For d = 0 take g := id. If p_{R+1+d} = p_{R+1} ∘ g, then
 p_{R+1+(d+1)} = p_{(R+1+d)+1} = p_{R+1+d} ∘ χ_{R+1+d, p_{R+1+d}} = p_{R+1} ∘ (g ∘ χ_{R+1+d, p_{R+1+d}}),
 and g ∘ χ_{R+1+d, p_{R+1+d}} is strictly increasing.

4. The diagonal. Define φ(j) := p_{j+1}(j), which is (χ_0 ∘ ⋯ ∘ χ_j)(j) in the parent's notation. For every j, φ(j+1) = p_{j+2}(j+1) = p_{j+1}(χ_{j+1,p_{j+1}}(j+1)), and χ_{j+1,p_{j+1}}(j+1) ≥ j + 1 > j. Since p_{j+1} is strictly increasing, φ(j+1) > p_{j+1}(j) = φ(j). Hence φ is strictly increasing (strictMono_nat_of_lt_succ).

5. Eventual subsequence property. Let R ≤ j. Step 3 with d := j − R gives a strictly increasing g with p_{j+1} = p_{R+1+(j−R)} = p_{R+1} ∘ g. So φ(j) = p_{R+1}(i) with i := g(j) ≥ j.

6. Comparison of limsups. Fix R and a closed F ⊆ B̄_R(0), and put a(k) := μ_k(F) ∈ [0, ∞]. In the complete lattice [0, ∞], limsup_j b(j) = inf_N sup_{j ≥ N} b(j) (limsup_eq_iInf_iSup_of_nat). Fix N. For every j ≥ max(N, R), step 5 gives i ≥ j ≥ N with a(φ(j)) = a(p_{R+1}(i)) ≤ sup_{i′ ≥ N} a(p_{R+1}(i′)). Hence
 limsup_j a(φ(j)) ≤ sup_{j ≥ max(N,R)} a(φ(j)) ≤ sup_{i ≥ N} a(p_{R+1}(i)).
 Taking the infimum over N gives limsup_j a(φ(j)) ≤ limsup_i a(p_{R+1}(i)).

7. Conclusion. For every R and every closed F ⊆ B̄_R(0), step 6 and (∗) give limsup_j μ_{φ(j)}(F) ≤ limsup_i μ_{p_{R+1}(i)}(F) ≤ ν_R(F). With step 4 (φ is strictly increasing) and step 2 (ν_R(ℝ^P) < ∞), φ and (ν_R)_{R∈ℕ} satisfy the statement. ∎

Implementation remark. A Lean proof of exactly this argument (about 55 lines), taking the frozen type of ind_md_closedBall_weak_subseq as a hypothesis, was compiled against the frozen project using only the axioms propext, Classical.choice and Quot.sound.

## Key steps

1. For each R and index map ψ, the sibling ind_md_closedBall_weak_subseq applied to (μ_{ψ(i)})_i gives χ_{R,ψ} and ν_{R,ψ}; choose them for all (R, ψ).
2. Nested maps p_0 = id and p_{R+1} = p_R ∘ χ_{R,p_R} are strictly increasing; ν_R := ν_{R,p_R} satisfies ν_R(ℝ^P) < ∞ and limsup_i μ_{p_{R+1}(i)}(F) ≤ ν_R(F).
3. Tails: p_{R+1+d} = p_{R+1} ∘ g with g strictly increasing (induction on d).
4. The diagonal φ(j) = p_{j+1}(j) is strictly increasing.
5. For j ≥ R, φ(j) = p_{R+1}(i) with i ≥ j, so limsup_j μ_{φ(j)}(F) ≤ limsup_i μ_{p_{R+1}(i)}(F) ≤ ν_R(F) (via limsup_eq_iInf_iSup_of_nat).

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
