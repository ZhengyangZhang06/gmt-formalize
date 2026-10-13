# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.covering-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.covering-a1.ball_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1–3 of the parent proof, together with the inclusion V ⊆ W from its Step 4. Mathematically this is Simon, Ch. 1, Remark 3.11(3): a measure on ℝ^n that is finite on compact sets has the symmetric Vitali property, proved there from the Besicovitch Covering Lemma 3.12. The balls are chosen inside an open set as in the proof of Simon Ch. 1, Theorem 3.13. Here the parent's integral inequality is replaced by an arbitrary admissibility predicate Q.

1. (Setting.) The hypothesis says μ(K) < ∞ for every compact K, which is exactly IsFiniteMeasureOnCompacts μ. In Lean, register it with `have : IsFiniteMeasureOnCompacts μ := ⟨hK⟩`. ℝ^P is a proper metric space, so every closed ball B̄_k(0), k ∈ ℕ, is compact and has finite μ-measure. Since ℝ^P = ⋃_{k∈ℕ} B̄_k(0), μ is σ-finite and therefore s-finite; on Euclid P, Lean infers the instance SFinite μ from IsFiniteMeasureOnCompacts μ. ℝ^P (Euclid P) is a second-countable metric space whose σ-algebra is the Borel σ-algebra, so open sets are measurable. Being a finite-dimensional real normed space, it has the Besicovitch covering property (Mathlib instance Besicovitch.instHasBesicovitchCovering, file Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean).

2. (Admissible radii.) For x ∈ ℝ^P put f(x) := {ρ ∈ ℝ : B̄_ρ(x) ⊆ W and Q(x, ρ)}. We claim that for every x ∈ E and every δ > 0, f(x) ∩ (0, δ) is nonempty.
- Since x ∈ E ⊆ W and W is open, there is R > 0 with B_R(x) ⊆ W (open ball; Metric.isOpen_iff).
- Since min(δ, R) > 0, the hypothesis gives ρ with 0 < ρ < min(δ, R) and Q(x, ρ).
- As ρ < R, the closed ball B̄_ρ(x) is contained in B_R(x) ⊆ W (closedBall_subset_ball).
Hence ρ ∈ f(x), and since 0 < ρ < δ, ρ ∈ f(x) ∩ (0, δ).

3. (Measurable Besicovitch covering theorem.) Apply Besicovitch.exists_disjoint_closedBall_covering_ae (Mathlib/MeasureTheory/Covering/Besicovitch.lean). Its arguments are the s-finite measure μ, the radius sets f, the set s := E, and the bound function R ≡ 1, which is positive at every point of E. Its covering hypothesis is exactly the claim of Step 2. No measurability of E is required. It gives a set t ⊆ ℝ^P and a function r : ℝ^P → ℝ such that:
- t is countable and t ⊆ E;
- r(x) ∈ f(x) ∩ (0, 1) for every x ∈ t;
- μ(E ∖ ⋃_{x∈t} B̄_{r(x)}(x)) = 0;
- t is pairwise disjoint for the family x ↦ B̄_{r(x)}(x).

4. (Unpacking.) Let x ∈ t. Since r(x) ∈ (0, 1), we have 0 < r(x). Since r(x) ∈ f(x), we have B̄_{r(x)}(x) ⊆ W and Q(x, r(x)). This gives (a). The pairwise disjointness from Step 3 is (b), and the null-set statement from Step 3 is (c). Together with the countability of t and t ⊆ E, the pair (t, r) has every required property. ∎

## Key steps

1. μ finite on compacts gives IsFiniteMeasureOnCompacts μ, hence μ is σ-finite and s-finite. Euclid P is second countable and Borel, and has the Besicovitch covering property (instHasBesicovitchCovering).
2. Admissible radii f(x) := {ρ : closedBall x ρ ⊆ W ∧ Q x ρ} meet every (0, δ) for x ∈ E. Take an open ball B_R(x) ⊆ W and apply the hypothesis with min(δ, R).
3. Besicovitch.exists_disjoint_closedBall_covering_ae with s = E and R ≡ 1 gives: t countable, t ⊆ E, r(x) ∈ f(x) ∩ (0,1), pairwise disjoint closed balls, and an uncovered part of E of measure zero.
4. Unpack r(x) ∈ f(x) ∩ (0,1) into 0 < r x, closedBall x (r x) ⊆ W and Q x (r x).

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `grep -n 'exists_disjoint_closedBall_covering_ae|exists_closedBall_covering_tsum_measure_le' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean; sed -n 1,80p, 640,670p, 800,900p of that file`
- `grep -rn 'instance.*HasBesicovitchCovering' mathlib/Mathlib/ (hit: Covering/BesicovitchVectorSpace.lean:499 instHasBesicovitchCovering); sed -n 490,505p`
- `grep -rn 'theorem hasSum_integral_iUnion|theorem integral_iUnion|theorem hasSum_integral_iUnion_ae|theorem integral_iUnion_ae' mathlib/Mathlib/; sed -n 310,345p Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `grep -rn 'theorem tsum_toReal_eq|theorem summable_toReal' mathlib/Mathlib/ (Topology/Algebra/InfiniteSum/ENNReal.lean:350, 491)`
- `grep -rn 'integrableOn_of_bounded' mathlib/Mathlib/MeasureTheory/ (Integral/IntegrableOn.lean:716 Measure.integrableOn_of_bounded)`
- `#check integral_biUnion in Probe.lean (unknown identifier: no match; use integral/hasSum over the countable subtype instead)`
- `Probe.lean: inferInstance for HasBesicovitchCovering (Euclid P), SFinite μ from IsFiniteMeasureOnCompacts μ, BorelSpace (Euclid P), SecondCountableTopology (Euclid P) (all succeed)`
- `python3 -I scan of dag.json lean_statements for PairwiseDisjoint, 'closedBall x (r x)', Besicovitch, HasSum, tsum, ∑', 'IntegrableOn g', 'μ W < ∞', Countable, and of ids containing null_sets/covering/vitali`
- `name-collision check of cbrldvc_exists_disjoint_closedBall_cover, cbrldvc_setIntegral_biUnion_le_mul_measure, cbrldvc_setIntegral_le_sub_of_subset against all 944 DAG lean_names, grep -rln cbrldvc over GMT/ and lake-packages-25730c7c/simongmt, and git log --all -S cbrldvc_`
- `python3 -I scripts/scope.py: verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem) and verifier/lean_contract.py validate_lean_statement on the 3 child statements`
- `lake env lean /tmp/cbrldvc-decomp-k7q2/{Probe,Children,Assembly,FullCheck}.lean`
- `grep -n -i besicovitch book/chapter-0*.txt; sed -n 770,880p book/chapter-01.txt (Simon Ch. 1 Remark 3.11(3), Lemma 3.12, Theorem 3.13)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-77789fb32b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-77789fb32b/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-77789fb32b/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/cbrldvc-decomp-k7q2/Probe.lean`
- `/tmp/cbrldvc-decomp-k7q2/Children.lean`
- `/tmp/cbrldvc-decomp-k7q2/Assembly.lean`
- `/tmp/cbrldvc-decomp-k7q2/FullCheck.lean`

Pinned Mathlib supplies everything the child proofs need:
- Besicovitch.exists_disjoint_closedBall_covering_ae: an s-finite measure, an arbitrary set s, admissible radii accumulating at 0 and a bound R give a countable t ⊆ s and r(x) ∈ f(x) ∩ (0, R(x)) with disjoint closed balls covering μ-almost all of s.
- The instance HasBesicovitchCovering for finite-dimensional real normed spaces.
- With IsFiniteMeasureOnCompacts μ, the instances SFinite, SecondCountableTopology and BorelSpace on Euclid P are inferred.
- hasSum_integral_iUnion, measure_iUnion, ENNReal.tsum_toReal_eq, ENNReal.summable_toReal, hasSum_le, Measure.integrableOn_of_bounded, setIntegral_union, integral_mono_ae, measure_sdiff and ENNReal.toReal_sub_of_le.
integral_biUnion does not exist, so the countable index set is handled through its subtype.

No accepted DAG node and no project or SimonGMT lemma states the covering, summation or complement bound. The only Vitali-type node, dorag_lip_vitali_two_measure_bound, is a different bound using 5r-balls. The three new cbrldvc_ names have no collisions.

All three child types elaborate in the replayed contract scope and pass the verifier's lexical check. Each has a complete proof without sorry. Together they prove the frozen parent type with axioms propext, Classical.choice and Quot.sound only.
