# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1.single_chart-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^m = EuclideanSpace ℝ (Fin m) (Lean `Eucl m`) with Euclidean norm |·| = ‖·‖; L(E, F) is the normed space of continuous linear maps E → F with the operator norm, carrying its Borel σ-algebra (Mathlib ContinuousLinearMap.instMeasurableSpace / instBorelSpace), so "Borel measurable" below is Lean's Measurable; fderiv ℝ g w is Mathlib's Fréchet derivative (the derivative where g is differentiable at w, and 0 otherwise). This is Steps 1–5 and 8 of the parent proof for a single chart, with the left inverse Λ of parent Step 0 taken as a hypothesis. Hypotheses: Λ : L(ℝⁿ, ℝ^P) → L(ℝ^P, ℝⁿ) is continuous on I := {A ∈ L(ℝⁿ, ℝ^P) : A injective} and, for every A ∈ I and v ∈ ℝ^P, Λ(A)∘A = id_{ℝⁿ} and |A(Λ(A)v)| ≤ |v|; Ω ⊆ ℝⁿ is open; Φ : ℝⁿ → ℝ^P is C¹; c > 0 and c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω; f : ℝ^P → ℝ^Q is arbitrary. Notation: S := Φ(Ω); DΦ(w) := fderiv ℝ Φ w ∈ L(ℝⁿ, ℝ^P) and B(w) := fderiv ℝ (f∘Φ) w ∈ L(ℝⁿ, ℝ^Q) for w ∈ ℝⁿ.

1. (Φ is injective on Ω.) If w, w′ ∈ Ω and Φ(w) = Φ(w′), the hypothesis gives c|w − w′| ≤ |Φ(w) − Φ(w′)| = 0; as c > 0, |w − w′| ≤ 0, so w = w′.

2. (S is Borel.) Ω is open, hence Borel; Φ is continuous (a C¹ map is continuous) and injective on Ω (step 1); ℝⁿ is Polish and ℝ^P carries its Borel σ-algebra. By the Lusin–Souslin theorem (the injective continuous image of a Borel subset of a Polish space is Borel; Kechris, Classical Descriptive Set Theory, Thm. 15.1; Mathlib MeasurableSet.image_of_continuousOn_injOn), S = Φ(Ω) is Borel. This is the conjunct MeasurableSet (Φ '' Ω).

3. (Inverse chart.) Let Ψ := Function.invFunOn Φ Ω : ℝ^P → ℝⁿ. For x ∈ S there is a ∈ Ω with Φ(a) = x, hence Ψ(x) ∈ Ω and Φ(Ψ(x)) = x (Mathlib invFunOn_mem, invFunOn_eq). For x, x′ ∈ S the hypothesis applied to Ψ(x), Ψ(x′) ∈ Ω gives c|Ψ(x) − Ψ(x′)| ≤ |Φ(Ψ(x)) − Φ(Ψ(x′))| = |x − x′|, i.e. |Ψ(x) − Ψ(x′)| ≤ c⁻¹|x − x′|. So Ψ is c⁻¹-Lipschitz on S, in particular continuous on S.

4. (DΦ(w) ∈ I for w ∈ Ω.) Let w ∈ Ω. Φ is C¹, hence differentiable at w. The sibling lemma lpf_wtc_cat_fderiv_lower_bound, applied with target dimension P (its Q := P), source dimension n, the map Φ, the open set Ω, the constant c and the point w, with the hypotheses Ω open, w ∈ Ω, Φ differentiable at w and c|v − v′| ≤ |Φ(v) − Φ(v′)| for v, v′ ∈ Ω, gives c|s| ≤ |DΦ(w)s| for all s ∈ ℝⁿ. If DΦ(w)s = 0 then c|s| ≤ 0, and c > 0 forces |s| ≤ 0, i.e. s = 0. A linear map with trivial kernel is injective, so DΦ(w) ∈ I.

5. (Borel measurability of G.)
   (a) Let Ψ̃(x) := Ψ(x) for x ∈ S and Ψ̃(x) := 0 otherwise (Set.piecewise). Ψ̃ is Borel: it is continuous on the Borel set S (steps 2, 3) and constant, hence continuous, on its complement (Mathlib ContinuousOn.measurable_piecewise).
   (b) The map w ↦ DΦ(w) = fderiv ℝ Φ w is continuous on ℝⁿ because Φ is C¹ (Mathlib ContDiff.continuous_fderiv), so x ↦ DΦ(Ψ(x)) is continuous on S (composition with Ψ, continuous on S by step 3). It maps S into I: for x ∈ S, Ψ(x) ∈ Ω (step 3), so DΦ(Ψ(x)) ∈ I (step 4). Since Λ is continuous on I, x ↦ Λ(DΦ(Ψ(x))) is continuous on S (ContinuousOn.comp). Let Λ̃(x) := Λ(DΦ(Ψ(x))) for x ∈ S and Λ̃(x) := 0 ∈ L(ℝ^P, ℝⁿ) otherwise; Λ̃ is Borel by ContinuousOn.measurable_piecewise as in (a).
   (c) B = fderiv ℝ (f∘Φ) : ℝⁿ → L(ℝⁿ, ℝ^Q) is Borel measurable for every map f∘Φ, with no regularity assumption (Mathlib measurable_fderiv). Hence x ↦ B(Ψ̃(x)) is Borel as a composition of Borel maps.
   (d) Define G(x) := B(Ψ̃(x)) ∘ Λ̃(x) ∈ L(ℝ^P, ℝ^Q). The composition map (T, R) ↦ T∘R : L(ℝⁿ, ℝ^Q) × L(ℝ^P, ℝⁿ) → L(ℝ^P, ℝ^Q) is continuous, being a bounded bilinear map (Mathlib isBoundedBilinearMap_comp), and both factors are finite-dimensional normed spaces, hence second countable. Therefore G, the composite of the Borel map x ↦ (B(Ψ̃(x)), Λ̃(x)) with a continuous map, is Borel (Mathlib Continuous.measurable2). This is the conjunct Measurable G.

6. (Chart identities.) Let x ∈ S and put w := Ψ(x); then w ∈ Ω and Φ(w) = x (step 3). Let A := DΦ(w); A ∈ I by step 4. As x ∈ S, Ψ̃(x) = w and Λ̃(x) = Λ(A), so G(x) = B(w) ∘ Λ(A).
   (i) For s ∈ ℝⁿ: G(x)(A s) = B(w)(Λ(A)(A s)) = B(w)(s), because Λ(A)∘A = id_{ℝⁿ} (hypothesis, A ∈ I). This is G x (fderiv ℝ Φ w s) = fderiv ℝ (f ∘ Φ) w s.
   (ii) For v ∈ ℝ^P put s := Λ(A)v ∈ ℝⁿ. Then |A s| = |A(Λ(A)v)| ≤ |v| (hypothesis, A ∈ I), and G(x)v = B(w)(Λ(A)v) = B(w)s.
   So w witnesses the last conjunct for x.

Steps 5(d), 2 and 6 prove the three conjuncts for this G. ∎ (Degenerate cases need no separate treatment: for n = 0 every linear map out of ℝ⁰ is zero and injective; if Ω = ∅ then S = ∅ and the last conjunct is vacuous.)

## Key steps

1. Φ is injective on Ω by the antilipschitz bound, so S = Φ(Ω) is Borel by Lusin–Souslin (MeasurableSet.image_of_continuousOn_injOn).
2. Ψ := invFunOn Φ Ω satisfies Ψ(x) ∈ Ω and Φ(Ψ(x)) = x on S and is c⁻¹-Lipschitz, hence continuous, on S.
3. By lpf_wtc_cat_fderiv_lower_bound (with Q := P), c|s| ≤ |DΦ(w)s|, so DΦ(w) is injective for every w ∈ Ω.
4. Ψ̃ := S.piecewise Ψ 0 and Λ̃ := S.piecewise (x ↦ Λ(DΦ(Ψ x))) 0 are Borel (ContinuousOn.measurable_piecewise, using continuity of Λ on injective maps), and x ↦ D(f∘Φ)(Ψ̃ x) is Borel (measurable_fderiv).
5. G(x) := D(f∘Φ)(Ψ̃ x) ∘ Λ̃(x) is Borel because composition of linear maps is continuous (Continuous.measurable2).
6. At x ∈ S with w := Ψ(x) and A := DΦ(w): G(x) = D(f∘Φ)(w)∘Λ(A), so G(x)(As) = D(f∘Φ)(w)s and G(x)v = D(f∘Φ)(w)(Λ(A)v) with |AΛ(A)v| ≤ |v|.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/{Contract,Submission}.lean against workspace GMT/Ch06/{Contract,Submission}.lean, and cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (all identical)`
- `rg -n 'theorem Measurable.find|theorem measurable_fderiv |theorem ContinuousOn.measurable_piecewise|theorem MeasurableSet.image_of_continuousOn_injOn|theorem invFunOn_mem|theorem invFunOn_eq|instMeasurableSpace|theorem Measurable.piecewise' Mathlib (snapshot)`
- `grep -rn isBoundedBilinearMap_comp Mathlib/Analysis/Normed/Operator/; grep -n 'theorem Continuous.measurable2' Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean; grep -rn of_dist_le_mul Mathlib/Topology/MetricSpace/Lipschitz.lean; theorem piecewise_eq_of_notMem in Mathlib/Data/Set/Piecewise.lean`
- `python3 over dag.json: lean_name/lean_statement matching fderiv|lower_bound|antilip|glue|gluing|find|measurable|borel|piecewise|chart|invFunOn|Nat.find|Λ (found accepted lpf_wtc_cat_fderiv_lower_bound and lpf_wtc_chart_image_measurable_locally_finite; no generic gluing lemma)`
- `python3 over dag.json: duplicate lean_name check (none), cross-branch reused-child edges (71, all accepted with open PR), node count 362, status counts`
- `git show proof-workspace/gmt-ch06/20261011t144224z-6e4735dbca/theorems/solutions/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9-656700a018:GMT/Ch06/Submission.lean and …char-1f4173ea67-7381c3335e:GMT/Ch06/Submission.lean (accepted proofs)`
- `git grep -c lpf_tde_mcd over all 1102 refs from git for-each-ref refs/heads refs/remotes -- GMT (no match, exit 1)`
- `verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') and child_modules (contract mode); verifier/lean_contract.validate_lean_statement on the 3 child types (all valid)`
- `lake build GMT.Ch06.Submission; lake env lean /tmp/mcd-decomp/{Stmts,Proofs,CmpCheck,Proofs2,CmpCheck2}.lean with #print axioms`
- `read nodes/root-deformation-a1-skeleton-polyhedral-a1/decomposition-v2.json (reuse format and controller rules) and swarm-project.json (max_nodes 1000, max_depth 6, max_children 12)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Function.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Piecewise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-co-7afa0393aa/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-skeleton-polyhedral-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/mcd-decomp/Proofs2.lean`
- `/tmp/mcd-decomp/CmpCheck2.lean`
- `/tmp/mcd-decomp/subproblems2.json`

Snapshot. It pins project d8d46c95 and Mathlib 25730c7c and holds the frozen Ch06 contract. Its project/GMT/Ch06/Contract.lean and Submission.lean are byte-identical to the workspace files, and Submission equals Contract.

Mathlib. Every lemma the children use is present with a compatible signature:
- Measurable.find (MeasurableSpace/Constructions.lean:515)
- measurable_fderiv, valid for any f (FDeriv/Measurable.lean:378)
- MeasurableSet.image_of_continuousOn_injOn, i.e. Lusin–Souslin (Polish/Basic.lean:821)
- ContinuousOn.measurable_piecewise and Continuous.measurable2 (BorelSpace/Basic.lean:523, 591)
- the Borel instMeasurableSpace/instBorelSpace on E →L[𝕜] F (BorelSpace/ContinuousLinearMap.lean:47–50)
- invFunOn_mem and invFunOn_eq (Data/Set/Function.lean:963–966)
- piecewise_eq_of_mem and piecewise_eq_of_notMem (Data/Set/Piecewise.lean:52–56)
- isBoundedBilinearMap_comp (Normed/Operator/BoundedLinearMaps.lean:379)
- LipschitzOnWith.of_dist_le_mul (MetricSpace/Lipschitz.lean:57)

DAG. The accepted lpf_wtc_cat_fderiv_lower_bound has exactly the content of Step 4 and is reused with an identical frozen type; 71 existing cross-branch reuse edges follow the same pattern. No accepted generic gluing lemma exists (no match), so countable_glue is new. The accepted lpf_wtc_chart_image_measurable_locally_finite would only replace the one-line Lusin–Souslin step, so it is not reused.

Kernel checks. Proofs2.lean and CmpCheck2.lean prove all three children with only propext, Classical.choice and Quot.sound. They also derive the exact frozen parent type from the children plus lpf_tde_continuous_left_inverse; sorryAx comes only from that uncle's stub.
