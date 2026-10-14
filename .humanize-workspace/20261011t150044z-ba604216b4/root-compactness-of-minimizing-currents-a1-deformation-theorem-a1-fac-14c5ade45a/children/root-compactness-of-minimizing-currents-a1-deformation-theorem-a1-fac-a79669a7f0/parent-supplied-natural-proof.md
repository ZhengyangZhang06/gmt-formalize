# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_geometry-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_geometry-a1.face_isometry_diam-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 and 4 of the parent proof. Uses the sibling result face_coord (Submission.cmcdtfrfg_face_coord).

1. In Euclid n (n = k or n = P), dist(u, v) = √(Σ_i dist(u_i, v_i)²), and dist(s, t) = |s − t| on ℝ (EuclideanSpace.dist_eq, Real.dist_eq).
2. Fix P, k, an injective ι and b. Let y, y' ∈ Euclid k, x := Φ(y) and x' := Φ(y'). Apply face_coord to (ι, b, y) and to (ι, b, y'). For every m : Fin k, x_{ι(m)} = b_{ι(m)} + y_m and x'_{ι(m)} = b_{ι(m)} + y'_m. For every l : Fin P with ι(m) ≠ l for all m, x_l = b_l = x'_l.
3. Put g(l) := dist(x_l, x'_l)² for l : Fin P and f(m) := dist(y_m, y'_m)² for m : Fin k. By step 2, g(l) = |b_l − b_l|² = 0 for l outside the range of ι, and g(ι(m)) = |(b_{ι(m)} + y_m) − (b_{ι(m)} + y'_m)|² = |y_m − y'_m|² = f(m).
4. Since ι is injective and g vanishes outside range ι, Σ_{l : Fin P} g(l) = Σ_{m : Fin k} g(ι(m)) = Σ_m f(m) (Fintype.sum_of_injective). Explicitly: split the sum over l into range ι and its complement. The complement contributes 0. ι : Fin k → range ι is a bijection, so the part over range ι reindexes to Σ_m g(ι(m)).
5. By step 1, dist(x, x') = √(Σ_l g(l)) = √(Σ_m f(m)) = dist(y, y'). This proves (a).
6. For (b), assume 0 ≤ y_i ≤ 1 and 0 ≤ y'_i ≤ 1 for all i. Then −1 ≤ y_m − y'_m ≤ 1, so f(m) = |y_m − y'_m|² ≤ 1 for each m. Hence Σ_m f(m) ≤ Σ_{m : Fin k} 1 = k, and since √ is monotone, dist(y, y') = √(Σ_m f(m)) ≤ √k.
7. Since ι : Fin k → Fin P is injective, k = card(Fin k) ≤ card(Fin P) = P (Fintype.card_le_of_injective). Hence √k ≤ √P.
8. By (a) and steps 6–7, dist(Φ(y), Φ(y')) = dist(y, y') ≤ √k ≤ √P. This proves (b). ∎

## Key steps

1. Euclidean distance is the square root of the sum of squared coordinate differences (EuclideanSpace.dist_eq).
2. By face_coord, the squared coordinate gaps of Φ(y) and Φ(y') vanish outside range ι and equal (y_m − y'_m)² at ι(m).
3. Reindexing the sum over Fin P along the injective ι (Fintype.sum_of_injective) gives dist(Φ y, Φ y') = dist(y, y').
4. On [0,1]^k each squared gap is ≤ 1, so dist(y, y') ≤ √k. Injectivity gives k ≤ P, hence the bound √P.

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
