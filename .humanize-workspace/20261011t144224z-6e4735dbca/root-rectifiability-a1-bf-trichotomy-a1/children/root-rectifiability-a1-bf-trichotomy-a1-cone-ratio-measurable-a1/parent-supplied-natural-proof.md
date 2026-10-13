# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.bf_trichotomy-a1`
- Child DAG node: `root.rectifiability-a1.bf_trichotomy-a1.cone_ratio_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2(a)-(c) of the parent-supplied proof of rectifiability_bf_trichotomy (F and Φ are Borel). This child is the instance of the sibling limsup_sup_measurable for the cones X_v(a,r,s).

1. Apply the sibling limsup_sup_measurable with Z := ℝ^N × (ℝ^N)^k, Y := ℝ^N, exponent k = m + 1, the given s-finite μ, the given δ, and
 G(r,s) := {((a,v),x) ∈ Z × ℝ^N : |x − a| < r and |L_v(x − a)| < s|x − a|}.
 For z = (a,v), {x : (z,x) ∈ G(r,s)} = X_v(a,r,s). So the function z ↦ limsup_{s→0⁺} sup_{0<r<δ} μ({x : (z,x) ∈ G(r,s)})/(rs)ᵏ produced by that lemma is exactly (a,v) ↦ Φ(a,v), by definitional unfolding of set-builder membership. It remains to verify the three hypotheses of the sibling.

2. G(r,s) is measurable. The following maps are continuous on Z × ℝ^N:
 - ((a,v),x) ↦ |x − a|;
 - ((a,v),x) ↦ |L_v(x − a)| = ‖(⟨v_i, x − a⟩)_i‖;
 - ((a,v),x) ↦ s|x − a|.
 This follows from continuity of the norm, of the inner product, of the evaluations v ↦ v_i and of WithLp.toLp into Eucl k. Hence G(r,s) = {|x − a| < r} ∩ {|L_v(x − a)| < s|x − a|} is open (isOpen_lt, IsOpen.inter). Z × ℝ^N is a finite product of second-countable spaces, so its Borel σ-algebra is the product σ-algebra (Prod.borelSpace), and open sets are measurable.

3. Monotone in s. If s ≤ s′ and |L_v(x − a)| < s|x − a|, then |L_v(x − a)| < s′|x − a|, because s|x − a| ≤ s′|x − a| (as |x − a| ≥ 0). So G(r,s) ⊆ G(r,s′).

4. Left continuous in r. Let r > 0.
 - For r′ ∈ (0,r), G(r′,s) ⊆ G(r,s), since |x − a| < r′ < r.
 - Conversely, let ((a,v),x) ∈ G(r,s) and put r′ := (|x − a| + r)/2. Then 0 < r′ < r and |x − a| < r′, so ((a,v),x) ∈ G(r′,s).
 Hence G(r,s) = ⋃_{r′∈(0,r)} G(r′,s).

5. By the sibling, Φ is measurable on ℝ^N × (ℝ^N)^k. ∎

This derivation compiles in Lean against the frozen statements, with the sibling as its only assumption.

Lean reference proof (appendix; written by the independent Lean reviewer of this decomposition and re-compiled by the author). It is compile-checked as a single declaration against the exact frozen statement inside `namespace GMT.Ch06` of a scratch copy of the frozen project (commit d8d46c9587747dee0751a1f780fcafdba16a3886, Lean v4.35.0-rc3, pinned Mathlib 25730c7c), with its declared sibling dependency Submission.rectifiability_bf_limsup_sup_measurable present as a theorem of its exact frozen type; with that sibling proved, #print axioms = [propext, Classical.choice, Quot.sound]. It introduces no auxiliary declarations.
```lean
theorem Submission.rectifiability_bf_cone_ratio_measurable : (∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ), SFinite μ → Measurable (fun p : Eucl N × (Fin (m + 1) → Eucl N) => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x p.1 < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) (x - p.1)) : Eucl (m + 1))‖ < s * ‖x - p.1‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0))) := by
  intro N m μ δ hμ
  refine Submission.rectifiability_bf_limsup_sup_measurable (Eucl N × (Fin (m + 1) → Eucl N)) (Eucl N) (m + 1) μ δ
    (fun r s => {q | dist q.2 q.1.1 < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.1.2 i) (q.2 - q.1.1)) : Eucl (m + 1))‖ < s * ‖q.2 - q.1.1‖}) hμ ?_ ?_ ?_
  · intro r s
    apply IsOpen.measurableSet
    apply IsOpen.inter
    · exact isOpen_lt (f := fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N => dist q.2 q.1.1) (by fun_prop) continuous_const
    · refine isOpen_lt (f := fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N => ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.1.2 i) (q.2 - q.1.1)) : Eucl (m + 1))‖) (g := fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N => s * ‖q.2 - q.1.1‖) ?_ (by fun_prop)
      refine continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp ?_)
      refine continuous_pi fun i => ?_
      exact ((continuous_apply i).comp (continuous_snd.comp continuous_fst)).inner (continuous_snd.sub (continuous_fst.comp continuous_fst))
  · intro r s s' hss' q hq
    exact ⟨hq.1, hq.2.trans_le (by gcongr)⟩
  · intro r s hr
    ext q
    simp only [mem_iUnion, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(dist q.2 q.1.1 + r) / 2, ⟨by positivity, by linarith⟩, by linarith, h2⟩
    · rintro ⟨r', ⟨hr'0, hr'r⟩, h1, h2⟩
      exact ⟨h1.trans hr'r, h2⟩
```

## Key steps

1. Instantiate limsup_sup_measurable with G(r,s) := {((a,v),x) : |x−a| < r, |L_v(x−a)| < s|x−a|}; its sections are the cones X_v(a,r,s).
2. G(r,s) is open (strict inequalities between continuous functions), hence measurable in the second-countable product.
3. G is monotone in s, and G(r,s) = ⋃_{0<r′<r} G(r′,s) for r > 0 (take r′ = (|x−a|+r)/2).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `git archive d8d46c9 into /tmp/bft-decomp-1791847446; cmp GMT/Ch06/Submission.lean (workspace) and project/GMT/Ch06/Contract.lean (snapshot) against the scratch copy (identical); lake build GMT.Ch06.Submission (success, 3152 jobs)`
- `rg -n 'theorem ae_ae_comm|theorem measurable_measure_prodMk_left |theorem _root_.Monotone.measure_iUnion|theorem _root_.Directed.measure_iUnion|theorem measure_biUnion_eq_iSup|theorem prod_apply_symm|theorem prod_apply |lemma IsSigmaCompact.image|theorem limsup_add_le|theorem limsup_const_mul_of_ne_top|theorem inner_single_left' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'measure_preimage_add_right|measure_univ_of_isAddLeftInvariant|measure_univ_of_isMulLeftInvariant' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n -i 'mickle|besicovitch.federer|purely.unrectifiable' local-references/197bdd4b88278494/mathlib/Mathlib local-references/197bdd4b88278494/project (no match); rg -n 'IsSigmaCompact.measurableSet' local-references/197bdd4b88278494/mathlib/Mathlib (no match)`
- `rg -n 'def dimensionalDensityQuotient|def realUnitBallVolume' lake-packages-25730c7c/simongmt/Poincare; sed -n 1,70p Chapter01/Densities.lean`
- `python3 verifier/gmt-compare.py contract_scope + child_modules (contract mode) for all 8 child statements; lake env lean Scratch/Chal_*.lean (0 errors)`
- `lake env lean Scratch/Names.lean and Scratch/Inst.lean (#check of the cited lemma names; instance checks for IsAddHaarMeasure, IsAddRightInvariant, SFinite of volume on Fin (m+1) → Eucl N, volume univ = ⊤ on Eucl (m+1), BorelSpace of the product types)`
- `lake env lean Scratch/Assembly.lean (parent from child stubs; #print axioms), Scratch/Iface1.lean (cone_ratio_measurable proved from the limsup_sup_measurable stub; ϑ_j instance), Scratch/Iface2.lean (OuterMeasure.mk + rectifiability_mickle_rado interface; later found vacuous because of a binder capture in the test example, and superseded by the complete slice_density_null proof)`
- `python3 lean_name collision scan of dag.json and nodes/*/decomposition-v*.json (658 names); byte comparison of reused lean_statement/title/statement against dag.json and the accepted handoffs`
- `lake env lean Verify/AllProofsFull.lean (independent reviewer's complete proofs of all six new children + accepted mickle_rado subtree + parent assembly; 0 errors; #print axioms [propext, Classical.choice, Quot.sound] for every declaration) and Verify/Standalone/<key>.lean for each new child with only its declared siblings stubbed (0 errors)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-trichotomy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1-limsup-eq-iinf-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-rectifiable-a1/decomposition-v1.json`
- `/tmp/bft-decomp-1791847446/Scratch/Assembly.lean`
- `/tmp/bft-decomp-1791847446/Scratch/Iface1.lean`
- `/tmp/bft-decomp-1791847446/Verify/AllProofsFull.lean`
- `/tmp/bft-decomp-1791847446/Verify/Standalone/slice_density_null.lean`
- `/tmp/bft-decomp-1791847446/Verify/Standalone/limsup_sup_measurable.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract, byte-identical to the workspace Submission.lean and to the scratch copy. Neither the snapshot Mathlib nor the project contains a Besicovitch–Federer, Mickle–Radó or purely-unrectifiable result (rg: no match), and Mathlib has no IsSigmaCompact.measurableSet. So all six new child obligations are genuine; the two accepted declarations rectifiability_mickle_rado and rectifiability_mickle_rado_limsup_eq_iInf are reused with byte-identical types. Every library input cited by the child proofs exists in the pinned environment: measurable_measure_prodMk_left, Measure.prod_apply and prod_apply_symm, Measure.ae_ae_comm (Prod.lean), Monotone.measure_iUnion, Directed.measure_iUnion and measure_biUnion_eq_iSup (Continuity.lean), measure_preimage_add_right and measure_univ_of_isAddLeftInvariant (additive forms of Group/Measure.lean), ENNReal.limsup_const_mul_of_ne_top (Order/Filter/ENNReal.lean), IsSigmaCompact.image, EuclideanSpace.inner_single_left (PiL2.lean:318), and dimensionalDensityQuotient and realUnitBallVolume (SimonGMT Chapter01/Densities.lean:39, Hausdorff.lean:34). ENNReal.limsup_add_le (ENNReal.lean:231) requires CountableInterFilter, which 𝓝[>]0 is not, so fibre_cone_comparison proves limsup subadditivity directly. In the scratch build, all eight child types elaborate in the comparator's exact child scope. The parent compiles from the five stubbed children it uses. Complete single-declaration Lean proofs of all six new children compile against their exact frozen types, using only their declared siblings, and with the accepted mickle_rado subtree the whole tree including Submission.rectifiability_bf_trichotomy compiles with axioms [propext, Classical.choice, Quot.sound].
