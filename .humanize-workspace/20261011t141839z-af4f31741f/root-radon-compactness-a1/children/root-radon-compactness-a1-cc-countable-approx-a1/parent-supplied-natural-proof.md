# Parent-supplied natural-language proof

- Parent DAG node: `root.radon_compactness-a1`
- Child DAG node: `root.radon_compactness-a1.cc_countable_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the "countable dense family" step (step 2) of the parent proof, i.e. the erratum-corrected form of the Alaoglu step in Simon's printed proof of Ch. 1, Theorem 4.16 (p. 37): "Let K_1, K_2, ... be an increasing sequence of compact sets with X = ∪_j K_j and let F_{j,k} : C(K_j) → ℝ be defined by F_{j,k}(f) = ∫_{K_j} f dμ_k, k = 1, 2, .... By the Alaoglu theorem there is a subsequence F_{j,k'} and a non-negative bounded functional F_j : C(K_j) → ℝ with F_{j,k'}(f) → F_j(f) for each f ∈ C(K_j)." ERRATUM (GMT/Ch01/README.md; SimonGMT Chapter01.simon_theorem_4_16_counterexample): the Alaoglu theorem only yields a subnet, not a subsequence; for second-countable X the step is made sequential by testing against a countable family of test functions which approximates every test function uniformly, with supports inside one compact set that depends only on the approximated function. This lemma constructs that family, for a general locally compact, Hausdorff, second-countable X (the parent applies it to the open subset U × G(N,n) of ℝ^N × G(N,n), as a subtype). It is step 1 (compact exhaustion) and step 2 (cutoff times countable dense family) of the parent proof of varifold_radon_compactness; instead of a countable dense subset of each C(X_{m+1}) in the sup norm, one countable dense subset of C(X,ℝ) for the compact-open topology (= uniform convergence on compact sets) is used, which serves all m at once.

Throughout, X is locally compact, Hausdorff and second countable; C_c(X,ℝ) is the set of continuous f : X → ℝ with compact topological support tsupport f = closure{f ≠ 0}.

1. Compact exhaustion. A locally compact second-countable space is σ-compact (Mathlib instance sigmaCompactSpace_of_locallyCompact_secondCountable). Hence there are compact sets E_0 ⊆ E_1 ⊆ E_2 ⊆ ... with E_m ⊆ interior(E_{m+1}) for every m and ⋃_m E_m = X (Mathlib: E := CompactExhaustion.choice X, with E.isCompact, E.subset_interior_succ, E.subset_succ). Moreover every compact C ⊆ X lies in some E_m (E.exists_superset_of_isCompact): the open sets interior(E_{m+1}) increase with m and cover X (each x lies in some E_m ⊆ interior(E_{m+1})), so finitely many of them, hence a single one, cover C, and interior(E_{m+1}) ⊆ E_{m+1}.

2. Cutoff functions. X is locally compact and Hausdorff, hence regular. Fix m. The set E_m is compact, the set (interior E_{m+1})ᶜ is closed, and they are disjoint because E_m ⊆ interior(E_{m+1}). By Urysohn's lemma for locally compact regular spaces (Mathlib exists_continuous_one_zero_of_isCompact) there is a continuous χ_m : X → ℝ with χ_m = 1 on E_m, χ_m = 0 on X ∖ interior(E_{m+1}), χ_m of compact support, and 0 ≤ χ_m(x) ≤ 1 for all x. Then {χ_m ≠ 0} ⊆ interior(E_{m+1}) ⊆ E_{m+1}, and E_{m+1} is closed (compact in a Hausdorff space), so tsupport χ_m ⊆ E_{m+1}; in particular χ_m(x) = 0 for x ∉ E_{m+1}.

3. A countable dense subset of C(X,ℝ). Equip the space C(X,ℝ) of continuous real functions with the compact-open topology. Since X is locally compact and second countable and ℝ is second countable, C(X,ℝ) is second countable, hence separable (Mathlib ContinuousMap.instSecondCountableTopology / ContinuousMap.instSeparableSpace, in the module Mathlib.Topology.ContinuousMap.SecondCountableSpace, which the Lean proof must import). As C(X,ℝ) is nonempty (it contains 0), there is a sequence (d_i)_{i∈ℕ} in C(X,ℝ) with dense range (Mathlib TopologicalSpace.denseSeq, denseRange_denseSeq). The compact-open topology of C(X,ℝ) is the topology of uniform convergence on compact sets: it is the topology of the compact-convergence uniformity, which has the basis of entourages {(h,h') : ∀ x ∈ L, (h(x), h'(x)) ∈ W} with L ⊆ X compact and W an entourage of ℝ (Mathlib ContinuousMap.compactConvergenceUniformSpace, ContinuousMap.hasBasis_compactConvergenceUniformity). Consequently, for every h ∈ C(X,ℝ), every compact L ⊆ X and every η > 0 the set {h' ∈ C(X,ℝ) : |h(x) − h'(x)| < η for all x ∈ L} is a neighbourhood of h (it is the ball around h for the entourage obtained from L and W = {(s,t) : |s − t| < η}; UniformSpace.ball_mem_nhds), so by density (Dense.inter_nhds_nonempty) it contains some d_i.

4. The family. Let ℕ → ℕ × ℕ, k ↦ (m(k), i(k)) := Nat.unpair k, be the standard bijection, with inverse (m, i) ↦ Nat.pair m i. Define g_k := χ_{m(k)} · d_{i(k)} (pointwise product). It is continuous, and it has compact support because χ_{m(k)} does (HasCompactSupport.mul_right); so g_k ∈ C_c(X,ℝ). Moreover tsupport g_k ⊆ tsupport χ_{m(k)} ⊆ E_{m(k)+1} (tsupport_mul_subset_left and step 2).

5. The approximation property. Let f ∈ C_c(X,ℝ). Since tsupport f is compact, step 1 gives m with tsupport f ⊆ E_m. Put K := E_{m+1}. Then K is compact and tsupport f ⊆ E_m ⊆ E_{m+1} = K. Now let η > 0. By step 3, applied to h = f (regarded as an element of C(X,ℝ)), L = E_{m+1} and η, there is i with |f(x) − d_i(x)| < η for all x ∈ E_{m+1}. Let k := Nat.pair m i; then (m(k), i(k)) = (m, i), so g_k = χ_m · d_i and, by step 4, tsupport g_k ⊆ E_{m+1} = K. It remains to show |f(x) − g_k(x)| ≤ η for every x ∈ X.
 (a) f(x) = χ_m(x) f(x) for every x: if x ∈ E_m then χ_m(x) = 1; if x ∉ E_m then x ∉ tsupport f (as tsupport f ⊆ E_m), so f(x) = 0 and both sides vanish.
 (b) Hence f(x) − g_k(x) = χ_m(x) f(x) − χ_m(x) d_i(x) = χ_m(x)(f(x) − d_i(x)), and since χ_m(x) ≥ 0, |f(x) − g_k(x)| = χ_m(x) |f(x) − d_i(x)|.
 (c) If x ∈ E_{m+1}, then |f(x) − d_i(x)| < η and 0 ≤ χ_m(x) ≤ 1, so |f(x) − g_k(x)| ≤ 1 · η = η.
 (d) If x ∉ E_{m+1}, then χ_m(x) = 0 by step 2, so |f(x) − g_k(x)| = 0 ≤ η (as η > 0).
Thus g = (g_k)_k has the required property: for every f the compact set K = E_{m+1} contains tsupport f, and for every η > 0 the index k = Nat.pair m i satisfies tsupport g_k ⊆ K and |f(x) − g_k(x)| ≤ η for all x. (If X is empty, all statements hold trivially and the same construction applies.) ∎

## Key steps

1. Compact exhaustion E_m of X (σ-compact since locally compact and second countable): E_m ⊆ interior E_{m+1}, every compact set lies in some E_m.
2. Urysohn cutoffs χ_m ∈ C_c(X): χ_m = 1 on E_m, 0 ≤ χ_m ≤ 1, tsupport χ_m ⊆ E_{m+1}.
3. C(X,ℝ) with the compact-open topology (= uniform convergence on compacts) is second countable, hence has a dense sequence d_i (needs import Mathlib.Topology.ContinuousMap.SecondCountableSpace).
4. g_{Nat.pair m i} := χ_m · d_i ∈ C_c(X,ℝ) with tsupport ⊆ E_{m+1}.
5. For tsupport f ⊆ E_m take K = E_{m+1}: f = χ_m f, so |f − χ_m d_i| = χ_m |f − d_i| ≤ η when sup_{E_{m+1}} |f − d_i| < η.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); lake-manifest.json revs vs git rev-parse HEAD of .lake/packages/mathlib (25730c7c759d108ef87ab70af2342a196760f79d) and .lake/packages/simongmt (2b3663083f3fe399b6296fb8eaee52169170e197)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `grep -n "structure Varifold\|def ofDomainMeasure\|theorem.*ofDomainMeasure\|domainMeasure\|instance\|finite_on\|measure :" simongmt Chapter08/Varifold.lean; sed -n 255,450p Chapter08/Varifold.lean`
- `cat simongmt Chapter01/CompactMetrizableCompactness.lean Chapter08/VarifoldConvergence.lean; grep -n '^theorem\|^def\|^noncomputable def\|^instance' Chapter01/SequentialCompactnessCounterexample.lean`
- `grep -n "theorem\|lemma\|def \|instance" mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean (rieszMeasure:65, integral_rieszMeasure:345, regular_rieszMeasure:357) and RieszMarkovKakutani/Basic.lean`
- `grep -rn "def mk₀\|structure PositiveLinearMap" mathlib/Mathlib/Algebra/Order/Module/PositiveLinearMap.lean (mk₀:206)`
- `grep -n "instance\|theorem\|lemma" mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean (instSecondCountableTopology:84, instSeparableSpace:108)`
- `grep -rn "theorem exists_continuous_one_zero_of_isCompact\|exists_tsupport_one_of_isOpen_isClosed" mathlib/Mathlib/Topology (UrysohnsLemma.lean:404,481)`
- `grep -n "theorem\|lemma\|instance" mathlib/Mathlib/Topology/UniformSpace/CompactConvergence.lean (hasBasis_compactConvergenceUniformity:200)`
- `grep -rn "theorem IsCompact.tendsto_subseq" mathlib/Mathlib (Sequences.lean:298); grep -rn "structure CompactExhaustion\|subset_interior_succ\|exists_superset_of_isCompact" mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `grep -rn "theorem norm_setIntegral_le_of_norm_le_const\|theorem setIntegral_eq_integral_of_forall_compl_eq_zero\|theorem integrableOn_iff_integrable_of_support_subset\|theorem Measure.integrableOn_of_bounded" mathlib/Mathlib`
- `sed -n 1660,1800p book/chapter-01.txt (printed Thm 4.14 proof end, 4.16 statement and proof); grep -n -i "4.16\|second countable\|subnet" GMT/Ch01/README.md; sed -n 285,312p GMT/Ch01/Contract.lean`
- `lake env lean Scratch/Probe.lean (#synth RegularSpace X, SigmaCompactSpace X, FirstCountableTopology (ℕ → ℝ), IsLocallyFiniteMeasure (RealRMK.rieszMeasure Λ): found; SeparableSpace C(X, ℝ): fails) and Scratch/Probe2.lean (with import Mathlib.Topology.ContinuousMap.SecondCountableSpace: ContinuousMap.instSeparableSpace)`
- `lake env lean Scratch/Child1.lean, Child2.lean, Child3.lean, Check.lean, Full.lean (import GMT.Ch08.Submission + comparator scope replay; full proofs of the three children and of the parent assembly; #print axioms)`
- `python: gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement on the three lean_statements; lake build GMT.Ch08.Submission (scratch, with child proofs) and lake env lean NodeChallenge{1,2,3}.lean, NodeSolution{1,2,3}.lean, NodeSolutionParent.lean`
- `grep -rl "radon_compactlySupported_countable_approx\|radon_exists_subseq_tendsto_integral\|radon_exists_measure_of_tendsto_integral" .humanize, simongmt Poincare, mathlib Mathlib (0 matches); python listing of dag.json node lean_names`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Order/Module/PositiveLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UniformSpace/CompactConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Content.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/SequentialCompactnessCounterexample.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch01/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-radon-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`

The snapshot is project 63436ae6 + Mathlib 25730c7c. The workspace packages are at the same revisions (simongmt 2b366308), and the snapshot Contract is byte-identical to the workspace Contract and Submission.

Mathlib supplies every ingredient of the corrected 4.16 proof, but not the theorem itself:
- RealRMK.rieszMeasure, integral_rieszMeasure and regular_rieszMeasure (RieszMarkovKakutani/Real.lean:65, 345, 357), plus isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts.
- PositiveLinearMap.mk₀ (PositiveLinearMap.lean:206).
- ContinuousMap.instSeparableSpace (ContinuousMap/SecondCountableSpace.lean:108). The contract does not import this module (#synth fails without it), so child 1's proof must add the import.
- exists_continuous_one_zero_of_isCompact (UrysohnsLemma.lean:404).
- ContinuousMap.hasBasis_compactConvergenceUniformity (CompactConvergence.lean:200).
- IsCompact.tendsto_subseq (Sequences.lean:298) and the CompactExhaustion API (SigmaCompact.lean:323–381).
- norm_setIntegral_le_of_norm_le_const and setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean).

SimonGMT has the following:
- Only the compact-metrizable version of 4.16 (CompactMetrizableCompactness.lean:32, 54), which is insufficient for the non-compact U × G.
- The counterexample to the printed 4.16 (SequentialCompactnessCounterexample.lean:141).
- Varifold.ofDomainMeasure (Varifold.lean:409), which needs exactly IsLocallyFiniteMeasure on the subtype U ×ˢ univ, with measure := μ.map Subtype.val.

No existing declaration states any of the three children, and the proposed names do not collide with anything.

Verified in Lean in a scratch copy with the comparator's scope replay:
- All three children have complete proofs.
- The parent's exact frozen type closes from them with axioms propext, Classical.choice, Quot.sound.
- Comparator-generated modules for each child elaborate, and each closes by exact Submission.X.
