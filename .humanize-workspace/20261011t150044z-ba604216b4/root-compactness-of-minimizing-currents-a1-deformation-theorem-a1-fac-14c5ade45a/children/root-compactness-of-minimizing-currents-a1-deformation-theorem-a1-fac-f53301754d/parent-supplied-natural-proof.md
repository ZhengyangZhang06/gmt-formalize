# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_geometry-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_geometry-a1.cube_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof. This is the fact vol(Q₁^k) = 1 that Simon uses as Lⁿ(F̆) = 1 in Ch. 6 §5, display (31).

Notation. For y : Euclid k = EuclideanSpace ℝ (Fin k), y i means the i-th coordinate (ofLp y) i. Here ofLp : Euclid k → (Fin k → ℝ) is the canonical identification. Q₁^k := {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}.

1. Fix k ∈ ℕ. The map ofLp : Euclid k → (Fin k → ℝ) is measure preserving, from volume on Euclid k to the product Lebesgue measure volume on Fin k → ℝ (Mathlib PiLp.volume_preserving_ofLp).
2. Let B := Set.pi univ (fun _ : Fin k => Ioo (0 : ℝ) 1) = {f : Fin k → ℝ | ∀ i, 0 < f i < 1}. For y : Euclid k, y ∈ Q₁^k ⇔ ∀ i, 0 < (ofLp y) i < 1 ⇔ ofLp y ∈ B. Hence Q₁^k = ofLp⁻¹(B).
3. B is a finite product of the measurable open intervals Ioo 0 1, so it is measurable (MeasurableSet.univ_pi with measurableSet_Ioo). Under a measure-preserving map, the preimage of a measurable set has the same measure as the set (MeasurePreserving.measure_preimage). Therefore volume(Q₁^k) = volume(ofLp⁻¹(B)) = volume(B).
4. By the volume formula for open boxes (Real.volume_pi_Ioo), volume(B) = ∏_{i : Fin k} ENNReal.ofReal(1 − 0) = ∏_{i : Fin k} 1 = 1. For k = 0 the product is empty and again equals 1.
5. Steps 3 and 4 give volume(Q₁^k) = 1. ∎

## Key steps

1. Q₁^k is the preimage of the box Set.pi univ (fun _ => Ioo 0 1) under ofLp : Euclid k → (Fin k → ℝ), which is measure preserving (PiLp.volume_preserving_ofLp).
2. The box is measurable, so its preimage has the same volume (MeasurePreserving.measure_preimage).
3. Real.volume_pi_Ioo gives volume(box) = ∏ ofReal(1 − 0) = 1. For k = 0 this is the empty product.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD = 25730c7c759d108ef87ab70af2342a196760f79d (matches manifest); git log -1 = b4d606db1da5da8fa2c0292ad4924d97de8b3c4b (matches manifest)`
- `python3 check: dag.json lean_statement of the selected node == parent-child-handoff.json subproblem.lean_statement (True)`
- `python3 -I /tmp/fgdecomp/scripts/scope.py verifier/gmt-compare.py GMT/Ch07/Contract.lean (contract_scope replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end)`
- `python3 scan of dag.json lean_name for cmcdtfrfg_cube_volume, cmcdtfrfg_face_coord, cmcdtfrfg_face_isometry_diam, cmcdtfrfg_face_separation and prefix cmcdtfrfg (all free among 1541 nodes)`
- `python3 scan of dag.json lean_statement for 'volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1', 'StrictMono p.1', 'single (ι', 'EuclideanSpace.single (p' (only the selected node and its cmcdtfr_ siblings; no identical accepted declaration to reuse)`
- `rg -n 'cmcdtfrfg_' project mathlib/Mathlib lake-packages-25730c7c/simongmt -g '*.lean' (no match)`
- `rg -n 'EuclideanSpace.single \(ι|orderEmbOfFin|range_inj' project/GMT -g '*.lean' (no match)`
- `rg -n 'theorem (WellFounded\.)?eq_strictMono_iff_eq_range|theorem StrictMono\.range_inj|theorem orderEmbOfFin_unique|theorem eq_of_subset_of_ncard_le|theorem card_le_of_injective|theorem volume_preserving_ofLp|theorem volume_pi_Ioo' mathlib/Mathlib`
- `rg -n 'theorem orderEmbOfFin_unique |theorem StrictMono.range_inj_of_wellFoundedLT|lemma prod_of_injective|theorem dist_apply_le|theorem one_le_abs|theorem card_le_of_injective ' mathlib/Mathlib`
- `rg -n 'CoeFun|theorem norm_apply_le|theorem dist_eq_of_L2' mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean; rg -n 'EuclideanSpace.single|theorem EuclideanSpace.dist_eq' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean; rg -n 'lemma ofLp_sum' mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean`
- `sed -n 1841,1920p book/chapter-06.txt (Simon Ch. 6 §5 displays (26)–(37); Lⁿ(F̆) = 1 is used in (31))`
- `lake env lean /tmp/fgdecomp/lean/Types.lean (four child types plus the frozen parent type, each as `theorem _root_.X : (T) := by sorry` after the replayed scope; no errors)`
- `lake env lean /tmp/fgdecomp/lean/Assembly.lean (FGAsm.check: cube_volume, face_isometry_diam and face_separation types imply the frozen parent type; axioms propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/fgdecomp/lean/Proofs1.lean, Proofs2.lean, Proofs3.lean, EndToEnd.lean (all four children proved; EndToEnd proves the exact frozen parent type from them; axioms propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-14c5ade45a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-14c5ade45a/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Group/Unbundled/Int.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/fgdecomp/lean/Types.lean`
- `/tmp/fgdecomp/lean/Assembly.lean`
- `/tmp/fgdecomp/lean/Proofs1.lean`
- `/tmp/fgdecomp/lean/Proofs2.lean`
- `/tmp/fgdecomp/lean/Proofs3.lean`
- `/tmp/fgdecomp/lean/EndToEnd.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace, and Submission.lean equals the contract. No project, SimonGMT or DAG declaration states the face-map coordinate, isometry or separation facts or the unit-cube volume with these types, so nothing can be reused, and the prefix cmcdtfrfg_ is free. Mathlib supplies every tool the child proofs cite: PiLp.volume_preserving_ofLp, Real.volume_pi_Ioo, WithLp.ofLp_sum, Pi.single_apply (EuclideanSpace.single is an abbrev for PiLp.single 2), EuclideanSpace.dist_eq, PiLp.dist_apply_le, Fintype.sum_of_injective (to_additive of prod_of_injective), Fintype.card_le_of_injective, Finset.orderEmbOfFin_unique, StrictMono.range_inj_of_wellFoundedLT and Int.one_le_abs. All four child types elaborate in the comparator's replayed scope. The children were proved in Lean and compose into the exact frozen parent type using only propext, Classical.choice and Quot.sound. Simon Ch. 6 §5 (31) is the use site of Lⁿ(F̆) = 1.
