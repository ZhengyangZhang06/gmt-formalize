# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1.truncation_sequence-a1`
- Child DAG node: `root.polyhedral_approximation-a1.truncation_sequence-a1.exhaustion_function-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1 of the parent proof. It constructs the exhaustion function of Simon 6.2, second paragraph of the printed proof (p. 169): "take any Lipschitz function φ on ℝ^{n+ℓ} such that φ > 0 in U, φ ≡ 0 in ℝ^{n+ℓ} ∖ U and such that {x : φ(x) > λ} ⊂⊂ U ∀ λ > 0". Errata: 'ans' = and; '{x D φ(x) > λ}' = {x : φ(x) > λ}. The book does not construct φ. This child states exactly the properties of φ that the parent uses.

Setting and notation. P ∈ ℕ and U ⊆ ℝ^P is open. |x| is the Euclidean norm. dist(x, F) := inf{|x − y| : y ∈ F} is Mathlib's Metric.infDist x F, with the convention infDist x ∅ = 0. B̄(0, r) is the closed ball of radius r about 0.

1. (Auxiliary function.) Let g(x) := 1/(1 + |x|). Then g(x) > 0 for every x.
 (a) g is 1-Lipschitz. For x, y ∈ ℝ^P, g(x) − g(y) = (|y| − |x|)/((1 + |x|)(1 + |y|)). Since (1 + |x|)(1 + |y|) ≥ 1 and ||y| − |x|| ≤ |x − y| (reverse triangle inequality), |g(x) − g(y)| ≤ |x − y|.
 (b) For t > 0, {x : g(x) ≥ t} ⊆ B̄(0, 1/t). Indeed, if 1/(1 + |x|) ≥ t then 1 ≥ t(1 + |x|) ≥ t|x|, so |x| ≤ 1/t.

2. (Case U = ℝ^P.) Put φ := g.
 (a) Property (i) holds by 1(a).
 (b) Property (ii). Let t > 0 and K_t := {x : φ(x) ≥ t}. K_t is closed, being the preimage of [t, ∞) under the continuous φ, and K_t ⊆ B̄(0, 1/t) by 1(b). Closed balls in ℝ^P are compact (Heine–Borel), so the closed subset K_t is compact. Trivially K_t ⊆ ℝ^P = U.
 (c) Property (iii). Let K ⊆ U be compact. If K = ∅, δ := 1 works vacuously. Otherwise the continuous φ attains its minimum on the nonempty compact set K at some x₀ ∈ K. Then δ := φ(x₀) = g(x₀) > 0 and φ(x) ≥ δ for all x ∈ K.

3. (Case U ≠ ℝ^P.) Then F := ℝ^P ∖ U is nonempty, and it is closed because U is open. Put φ(x) := min{dist(x, F), g(x)}.
 (a) Property (i). x ↦ dist(x, F) is 1-Lipschitz (Mathlib lipschitz_infDist_pt), and g is 1-Lipschitz by 1(a). The pointwise minimum of an L₁-Lipschitz and an L₂-Lipschitz function is max(L₁, L₂)-Lipschitz (LipschitzWith.min), so φ is 1-Lipschitz. In particular φ is continuous.
 (b) φ > 0 on U. If x ∈ U then x ∉ F. Since F is closed and nonempty, dist(x, F) > 0 (IsClosed.notMem_iff_infDist_pos). Also g(x) > 0, so φ(x) > 0.
 (c) Property (ii). Let t > 0 and K_t := {x : φ(x) ≥ t}.
  - K_t is closed because φ is continuous.
  - If x ∈ K_t then g(x) ≥ φ(x) ≥ t, so K_t ⊆ B̄(0, 1/t) by 1(b). Being closed and bounded, K_t is compact.
  - Suppose x ∈ K_t but x ∉ U. Then x ∈ F, so dist(x, F) = 0 (infDist_zero_of_mem). Hence φ(x) = min{0, g(x)} ≤ 0 < t ≤ φ(x), a contradiction. Therefore K_t ⊆ U.
 (d) Property (iii). Let K ⊆ U be compact. If K = ∅, δ := 1 works. Otherwise the continuous φ attains its minimum on K at some x₀ ∈ K ⊆ U. Then δ := φ(x₀) > 0 by (b), and φ(x) ≥ δ for all x ∈ K.

4. (Conclusion.) In either case φ satisfies (i), (ii) and (iii). ∎

Formalization notes:
- The two cases are `by_cases U = univ`; nonempty_compl turns U ≠ univ into (Uᶜ).Nonempty.
- Compactness of K_t: (isCompact_closedBall 0 (1/t)).of_isClosed_subset (isClosed_le continuous_const hφ.continuous).
- Minimum on K: IsCompact.exists_isMinOn.
- A trial Lean proof of exactly this frozen statement compiles in the comparator scope with axioms [propext, Classical.choice, Quot.sound].

## Key steps

1. g(x) = 1/(1+|x|) is positive and 1-Lipschitz, and {g ≥ t} ⊆ B̄(0, 1/t) for t > 0.
2. If U = ℝ^P, take φ = g. Its superlevel sets are closed subsets of compact balls; a positive minimum on a nonempty compact K gives δ.
3. If U ≠ ℝ^P, take φ = min(dist(·, ℝ^P∖U), g). It is 1-Lipschitz as a minimum of 1-Lipschitz functions, and positive on U because ℝ^P∖U is closed and nonempty.
4. {φ ≥ t} is closed, lies in B̄(0, 1/t), and lies in U because dist(·, ℝ^P∖U) = 0 off U; hence it is compact and contained in U.
5. The continuous φ, positive on U, attains a positive minimum δ on each nonempty compact K ⊆ U (δ = 1 if K = ∅).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean and Submission.lean vs workspace GMT/Ch06/Contract.lean and Submission.lean (byte-identical; Submission = Contract)`
- `rg -n 'exhaustion|cutoff|cut-off' snapshot project/GMT (no match)`
- `grep -c / grep -rl 'polyhedral_approx_exhaustion_function' and 'polyhedral_approx_boundary_mass_cutoff' in dag.json, nodes/, snapshot project/, GMT/ (0 matches)`
- `python3 dag.json node listing (statuses, lean_names; accepted: cmb_exists_compactly_contained_exhaustion, cmb_exists_countable_dense_testForms)`
- `grep -n '^def |^theorem ' simongmt Chapter06/Mass.lean, Currents.lean, CurrentLocalEquality.lean, Forms.lean`
- `grep -rn 'covectorEuclideanNorm_smul|massOn_add|massOn_le_add' simongmt (no match)`
- `grep -rn 'exists_contMDiffMap_one_nhds_of_subset_interior|exists_cthickening_subset_open|Filter.EventuallyEq.extDeriv_eq|Filter.EventuallyEq.fderiv_eq|setIntegral_congr_fun₀|setIntegral_indicator|lipschitz_infDist_pt|LipschitzWith.min|notMem_iff_infDist_pos|norm_fderiv_le_of_lipschitz|ae_lt_top|ae_restrict_mem|ae_neBot|exists_nat_one_div_lt|closure_lt_subset_le' Mathlib`
- `cmp snapshot mathlib files vs lake-packages-25730c7c/mathlib (12 cited files identical)`
- `sed -n 1955,2000p book/chapter-06.txt (Simon 6.2 printed proof)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on both child statements (both pass unchanged)`
- `lake build GMT.Ch06.Submission (scratch /tmp/ts_decomp_1791763526 = git archive d8d46c9 + pinned packages)`
- `lake env lean Scratch/Stmts.lean; Scratch/C1.lean; Scratch/C2.lean; Scratch/C2NoImport.lean; Scratch/Assembly.lean; Scratch/Full.lean; Scratch/Inst.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-truncation-sequence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1/decomposition-v1.json`
- `/tmp/ts_decomp_1791763526/Scratch/Stmts.lean`
- `/tmp/ts_decomp_1791763526/Scratch/C1.lean`
- `/tmp/ts_decomp_1791763526/Scratch/C2.lean`
- `/tmp/ts_decomp_1791763526/Scratch/C2NoImport.lean`
- `/tmp/ts_decomp_1791763526/Scratch/Assembly.lean`
- `/tmp/ts_decomp_1791763526/Scratch/Full.lean`
- `/tmp/ts_decomp_1791763526/Scratch/Inst.lean`

Snapshot provenance:
- The snapshot is project d8d46c95 with Mathlib 25730c7c. Its Contract and Submission are byte-identical to the workspace, and Submission equals Contract, with no Submission.* declarations.
- The 12 cited snapshot Mathlib files are byte-identical to the pinned packages.

What the sources provide:
- SimonGMT supplies massOn/mass (sSup over massAdmissibleOn), GeometricCurrentOn.le_massOn, boundary_apply/exteriorDerivativeTestOn (∂T(ψ) = T(dψ) with d = extDeriv), testFormOnInclusion_coe and covectorEuclideanNorm.
- SimonGMT has no covectorEuclideanNorm homogeneity lemma and no massOn subadditivity. The first is proved inside child boundary_mass_cutoff; the second is a short inline step of the parent.
- Mathlib at the pin provides every tool used:
  - smooth Urysohn: exists_contMDiffMap_one_nhds_of_subset_interior, reachable from the existing imports;
  - IsCompact.exists_cthickening_subset_open and Filter.EventuallyEq.extDeriv_eq;
  - integration: setIntegral_congr_fun₀ and setIntegral_indicator;
  - Lipschitz and distance lemmas: lipschitz_infDist_pt, LipschitzWith.min, IsClosed.notMem_iff_infDist_pos and norm_fderiv_le_of_lipschitz;
  - measure-theory lemmas: ae_lt_top, ae_restrict_mem and ae_neBot;
  - exists_nat_one_div_lt and closure_lt_subset_le.
- Book p. 169 (chapter-06.txt, lines 1962–1996) prints only the existence of φ and the appeal to 4.5. The children's proofs are therefore extracted from the supplied parent proof.

Names and reuse:
- Neither proposed name occurs anywhere in the DAG, the node files or the project.
- The accepted exhaustion lemma cmb_exists_compactly_contained_exhaustion has a different type, so it is not reused.

Scratch Lean checks:
- Both child statements pass validate_lean_statement and elaborate in the comparator child scope.
- Trial proofs of both exact child types compile with [propext, Classical.choice, Quot.sound].
- The parent's exact frozen type compiles, with no sorry, from the two children plus the parent's three declared sibling dependencies (exact frozen types).
- Combined comparator-style targets confirm the exact types match.
