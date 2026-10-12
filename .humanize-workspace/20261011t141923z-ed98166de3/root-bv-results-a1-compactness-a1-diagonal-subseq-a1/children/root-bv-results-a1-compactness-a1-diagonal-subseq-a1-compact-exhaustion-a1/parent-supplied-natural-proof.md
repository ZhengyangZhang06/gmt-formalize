# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.compactness-a1.diagonal_subseq-a1`
- Child DAG node: `root.bv_results-a1.compactness-a1.diagonal_subseq-a1.compact_exhaustion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2, Theorem 2.6 (p. 50). The printed proof reduces the claim to precompactness in L¹_loc(U), and the reviewed proof supplied to node root.bv_results-a1.compactness-a1.diagonal_subseq-a1 (step A2 of root.bv_results-a1.compactness-a1) turns precompactness on every compact subset into an L¹_loc-convergent subsequence by compact exhaustion and diagonal extraction. This child is step 1 of that proof (the compact exhaustion), extracted as a self-contained statement with the details filled in. Notation: ℝⁿ = Rn n = EuclideanSpace ℝ (Fin n), a proper metric space; Uᶜ = ℝⁿ ∖ U; infEDist(x, A) = Metric.infEDist x A ∈ [0, ∞] (infEDist(x, ∅) = ∞); ofReal = ENNReal.ofReal.

Claim. If U ⊆ ℝⁿ is open, there are sets Q_j (j ∈ ℕ) with (i) every Q_j compact, (ii) Q_j ⊆ U, (iii) Q_i ⊆ Q_j for i ≤ j (Monotone Q), and (iv) every compact K ⊆ U contained in some Q_j.

1. Definition. For j ∈ ℕ put Q_j := closedBall(0, j + 1) ∩ {x : ofReal(1/(j + 1)) ≤ infEDist(x, Uᶜ)}. No case distinction is needed. If U = ℝⁿ then Uᶜ = ∅, infEDist(x, ∅) = ∞ and Q_j = closedBall(0, j + 1). If U = ∅ then infEDist(x, Uᶜ) = 0 < ofReal(1/(j + 1)) and every Q_j is empty. The case n = 0 is covered by the same argument.

2. Property (i), compactness. The function x ↦ infEDist(x, Uᶜ) is continuous: it is 1-Lipschitz (Metric.continuous_infEDist). Hence {x : ofReal(1/(j + 1)) ≤ infEDist(x, Uᶜ)} is closed (isClosed_le continuous_const continuous_infEDist). The ball closedBall(0, j + 1) is compact because ℝⁿ is proper (isCompact_closedBall). The intersection of a compact set with a closed set is compact (IsCompact.inter_right), so Q_j is compact.

3. Property (ii), Q_j ⊆ U. Let x ∈ Q_j and suppose x ∉ U. Then x ∈ Uᶜ, so infEDist(x, Uᶜ) = 0 (Metric.infEDist_zero_of_mem). But 1/(j + 1) > 0, so ofReal(1/(j + 1)) > 0 (ENNReal.ofReal_pos). This contradicts ofReal(1/(j + 1)) ≤ infEDist(x, Uᶜ) = 0. Hence x ∈ U.

4. Q_j ⊆ interior Q_{j+1}. Let x ∈ Q_j. Put O := ball(0, j + 2) ∩ {y : ofReal(1/(j + 2)) < infEDist(y, Uᶜ)}.
 (a) O is open. The ball is open, and the strict superlevel set of the continuous function y ↦ infEDist(y, Uᶜ) is open (isOpen_lt continuous_const continuous_infEDist).
 (b) x ∈ O. First, ‖x‖ ≤ j + 1 < j + 2. Second, 0 < 1/(j + 2) < 1/(j + 1) (one_div_lt_one_div_of_lt), so ofReal(1/(j + 2)) < ofReal(1/(j + 1)) (ENNReal.ofReal_lt_ofReal_iff). Since ofReal(1/(j + 1)) ≤ infEDist(x, Uᶜ), we get ofReal(1/(j + 2)) < infEDist(x, Uᶜ).
 (c) O ⊆ Q_{j+1}. Let y ∈ O. Then ‖y‖ < j + 2 = (j + 1) + 1, so y ∈ closedBall(0, (j + 1) + 1). Also ofReal(1/((j + 1) + 1)) = ofReal(1/(j + 2)) < infEDist(y, Uᶜ), so the inequality defining Q_{j+1} holds.
 So O is open and x ∈ O ⊆ Q_{j+1}, i.e. x ∈ interior Q_{j+1} (mem_interior).

5. Property (iii), monotonicity. By step 4 and interior Q_{j+1} ⊆ Q_{j+1} (interior_subset), Q_j ⊆ Q_{j+1} for every j. Induction on j − i gives Q_i ⊆ Q_j for all i ≤ j (monotone_nat_of_le_succ).

6. Every point of U lies in some Q_j. Let x ∈ U.
 (a) infEDist(x, Uᶜ) ≠ 0. Uᶜ is closed because U is open, so closure Uᶜ = Uᶜ (IsClosed.closure_eq). If infEDist(x, Uᶜ) = 0, then x ∈ closure Uᶜ = Uᶜ (Metric.mem_closure_iff_infEDist_zero), contradicting x ∈ U.
 (b) By ENNReal.exists_inv_nat_lt there is m ∈ ℕ with (m : [0,∞])⁻¹ < infEDist(x, Uᶜ).
 (c) Choose j ∈ ℕ with j ≥ max(‖x‖, m) (exists_nat_ge). Then ‖x‖ ≤ j + 1, so x ∈ closedBall(0, j + 1).
 (d) Since m ≤ j + 1, ofReal(1/(j + 1)) = ((j + 1 : [0,∞]))⁻¹ ≤ (m : [0,∞])⁻¹ < infEDist(x, Uᶜ). The lemmas are ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_natCast and ENNReal.inv_le_inv. Hence x ∈ Q_j.

7. Property (iv), absorption of compact sets. Let K ⊆ U be compact. For j ∈ ℕ put V_j := interior Q_{j+1}.
 (a) Each V_j is open (isOpen_interior).
 (b) The V_j are increasing, so the family is directed: i ≤ j gives Q_{i+1} ⊆ Q_{j+1} by step 5, and interior is monotone (interior_mono).
 (c) The V_j cover K: each x ∈ K lies in U, hence in some Q_j by step 6, hence in V_j by step 4.
 (d) A compact set covered by a directed family of open sets lies in a single member of the family; the index type ℕ is nonempty (IsCompact.elim_directed_cover). So K ⊆ V_J for some J, and V_J ⊆ Q_{J+1}.

8. Steps 2, 3, 5 and 7 prove (i)–(iv) for Q = (Q_j)_{j∈ℕ}. ∎

(An equivalent Lean route: the subtype ↥U is locally compact (IsOpen.locallyCompactSpace) and σ-compact (second countable), so CompactExhaustion.choice ↥U exists, and its images under Subtype.val have properties (i)–(iv) by CompactExhaustion.exists_superset_of_isCompact. The explicit construction above is a complete proof on its own.)

## Key steps

1. Define Q_j := closedBall(0, j+1) ∩ {x : ofReal(1/(j+1)) ≤ infEDist(x, Uᶜ)}; the cases U = ℝⁿ, U = ∅ and n = 0 need no special treatment.
2. Q_j is compact: a compact closed ball meets the closed superlevel set of the continuous map x ↦ infEDist(x, Uᶜ).
3. Q_j ⊆ U: off U the distance infEDist(x, Uᶜ) is 0 < ofReal(1/(j+1)).
4. Q_j ⊆ interior Q_{j+1}: the open set ball(0, j+2) ∩ {ofReal(1/(j+2)) < infEDist(·, Uᶜ)} contains Q_j and lies in Q_{j+1}; hence Q is monotone.
5. Each x ∈ U lies in some Q_j: infEDist(x, Uᶜ) ≠ 0 because Uᶜ is closed, then choose j ≥ max(‖x‖, m) with m⁻¹ < infEDist(x, Uᶜ).
6. A compact K ⊆ U is covered by the increasing open sets interior Q_{j+1}; IsCompact.elim_directed_cover gives K ⊆ Q_{J+1}.

## Reference use

### local-project

Queries:
- `cat local-references/ff09f3909baeeae7/manifest.json (mode local-project; project 1b1689a8deba89d58b36b1a04dba493693824437; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch02/Contract.lean and Submission.lean against the workspace copies (identical); cmp snapshot mathlib files against lake-packages-25730c7c/mathlib (SigmaCompact, LocallyIntegrable, LpSeminorm/Defs, LpSpace/Basic, Sequences, Bases, Compactness/Compact, UniformSpace/Cauchy, MetricSpace/Pseudo/Basic, MetricSpace/HausdorffDistance: identical)`
- `rg -n 'structure CompactExhaustion|theorem exists_superset_of_isCompact|def choice|exists_compact_exhaustion|IsOpen.exists_iUnion_isCompact|isCompact_exhaustion|exists_seq_isCompact|IsOpen.sigmaCompact|isSigmaCompact_of_isOpen|IsOpen.isSigmaCompact' Mathlib`
- `rg -n 'theorem locallyIntegrableOn_iff|theorem LocallyIntegrableOn.integrableOn_compact_subset|theorem tendsto_subseq|theorem TotallyBounded.isCompact_of_isClosed|theorem totallyBounded_iff|theorem edist_toLp_toLp|theorem eLpNorm_one_eq_lintegral_enorm|theorem isCompact_univ_pi|instance.*FirstCountableTopology' Mathlib`
- `sed -n 115,140p Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean (eLpNorm_one_eq_lintegral_enorm requires AEStronglyMeasurable)`
- `grep -rlE 'Kolmogorov.?Riesz|Frechet.?Kolmogorov|Fréchet.?Kolmogorov|Rellich' Mathlib (no match)`
- `grep -n 'TendstoLocallyInL1On|IsRelativelyCompactIn|def |theorem |lemma ' simongmt/Poincare/SimonGMT/Chapter02/BV.lean, then sed -n 105,260p`
- `python3 -I scan of dag.json lean_statements for Monotone|exhaust|TendstoLocallyInL1On|StrictMono|Lp; grep lean_name over nodes/*/decomposition-v*.json; git grep of the 3 proposed names over all refs (no match)`
- `python3 -I gen.py (verifier gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement) -> Checks/NodeChallenge_00..02.lean and Checks/Assembly.lean; lake env lean on each against a scratch olean of GMT.Ch02.Submission`
- `lake env lean Prove/ChildA.lean, Prove/ChildB.lean, Prove/ChildC.lean, Review/Assembly.lean, Review/FullChain.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-compactness-a1-diagonal-subseq-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/diagsub-decomp-jHC3Ee/proj/Checks/NodeChallenge_00.lean`
- `/tmp/diagsub-decomp-jHC3Ee/proj/Checks/NodeChallenge_01.lean`
- `/tmp/diagsub-decomp-jHC3Ee/proj/Checks/NodeChallenge_02.lean`
- `/tmp/diagsub-decomp-jHC3Ee/proj/Checks/Assembly.lean`
- `/tmp/diagsub-decomp-jHC3Ee/proj/Prove/ChildA.lean`
- `/tmp/diagsub-decomp-jHC3Ee/proj/Prove/ChildB.lean`
- `/tmp/diagsub-decomp-jHC3Ee/proj/Prove/ChildC.lean`
- `/tmp/diagsub-decomp-jHC3Ee/proj/Review/Assembly.lean`
- `/tmp/diagsub-decomp-jHC3Ee/proj/Review/FullChain.lean`

Snapshot integrity: Contract.lean and Submission.lean in the snapshot are byte-identical to the workspace copies. The cited mathlib files are identical to the compiled lake package (commit 25730c7c). TendstoLocallyInL1On (SimonGMT BV.lean) means ∀ compact K ⊆ U, ∫⁻_K‖v_i − u‖ₑ → 0.

Library gaps:
- Mathlib has CompactExhaustion only for whole (σ-compact, locally compact) spaces. There is no lemma for an open subset that absorbs compact sets, so compact_exhaustion is new.
- Mathlib has no L¹ compactness theorem (no Kolmogorov–Riesz/Rellich/Fréchet–Kolmogorov match) and no gluing lemma for L¹_loc limits, so simultaneous_subseq and glue_limits are new.
- Their building blocks all exist and resolve: Lp completeness, Lp.edist_toLp_toLp/edist_def, eLpNorm_one_eq_lintegral_enorm, TotallyBounded.isCompact_of_isClosed, isCompact_univ_pi, the countable-product FirstCountableTopology instance, IsCompact.tendsto_subseq, locallyIntegrableOn_iff, IsCompact.elim_directed_cover and the infEDist API.
- In this mathlib eLpNorm_one_eq_lintegral_enorm needs AEStronglyMeasurable, and the child proofs account for this.

DAG check: no DAG node has an identical frozen type to reuse. eilenberg_compact_exhaustion and convex_open_exists_inner_exhaustion state different facts. The three new names are unreserved.

Lean checks: all three child types elaborate in the comparator scope and are proved outright with axioms [propext, Classical.choice, Quot.sound]. The assembly from the three types to the exact frozen parent type, and the full chain, compile with the same axioms.
