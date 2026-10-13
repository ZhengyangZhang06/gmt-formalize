# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.lipschitz_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent's supplied proof ("φ_r is the componentwise McShane extension of ψ|{d ≥ r} (Mathlib LipschitzOnWith.extend_real for each coordinate x ↦ ψ(x)_i ...). Then φ_r : ℝ^P → ℝ^P is (√P c_R/r)-Lipschitz and φ_r = ψ on {d ≥ r}"), for an arbitrary set S and constant K. Coordinates: for v ∈ ℝ^P = EuclideanSpace ℝ (Fin P) write v_i := v i; then ‖v‖² = Σ_i v_i² and dist(v, w)² = Σ_i (v_i − w_i)² (EuclideanSpace.norm_eq, EuclideanSpace.dist_eq).

1. (Coordinates are K-Lipschitz on S.) Fix i ∈ Fin P and put ψ_i(x) := ψ(x)_i. For x, y ∈ S, |ψ_i(x) − ψ_i(y)| = |(ψ(x) − ψ(y))_i| ≤ ‖ψ(x) − ψ(y)‖ ≤ K·dist(x, y), because a single coordinate is bounded by the Euclidean norm (v_i² ≤ Σ_j v_j²). So ψ_i is LipschitzOnWith K on S (LipschitzOnWith.of_dist_le_mul).
2. (McShane.) By LipschitzOnWith.extend_real there is g_i : ℝ^P → ℝ which is K-Lipschitz on ℝ^P and equals ψ_i on S. Choose such g_i for every i (finitely many).
3. (Definition.) Let φ(x) ∈ ℝ^P be the vector with coordinates φ(x)_i = g_i(x) (the EuclideanSpace vector of the function i ↦ g_i(x), e.g. WithLp.toLp 2 (fun i => g_i x) / (EuclideanSpace.equiv _ _).symm).
4. (Lipschitz constant.) For x, y ∈ ℝ^P, dist(φ(x), φ(y))² = Σ_i (g_i(x) − g_i(y))² ≤ Σ_i K²·dist(x, y)² = P·K²·dist(x, y)². Taking square roots (Real.sqrt_le_sqrt, √(P K² D²) = √P·K·D for K, D ≥ 0), dist(φ(x), φ(y)) ≤ √P·K·dist(x, y). Since the real number underlying NNReal.sqrt P * K is √P·K (Real.coe_sqrt, NNReal.coe_natCast), φ is LipschitzWith (NNReal.sqrt P * K) (LipschitzWith.of_dist_le_mul).
5. (Agreement on S.) For x ∈ S and every i, φ(x)_i = g_i(x) = ψ_i(x) = ψ(x)_i, so φ(x) = ψ(x) (equality of coordinates). Hence EqOn φ ψ S. ∎

## Key steps

1. Each coordinate ψ_i is K-Lipschitz on S (a coordinate is bounded by the Euclidean norm).
2. Extend each ψ_i to a K-Lipschitz g_i on ℝ^P (LipschitzOnWith.extend_real) and set φ(x) := (g_i(x))_i.
3. dist(φ x, φ y)² = Σ_i (g_i x − g_i y)² ≤ P K² dist(x, y)², so φ is √P·K-Lipschitz; φ = ψ on S coordinatewise.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n -i 'deformation|skeleton|telescop' project/GMT -g '*.lean'`
- `rg -n 'theorem LipschitzOnWith.extend_real|theorem LipschitzOnWith.extend_pi' mathlib/Mathlib`
- `rg -n 'theorem Monotone.ae_differentiableAt|theorem measurable_deriv|theorem hasDerivAt_iff_tendsto_slope_zero|theorem HasDerivAt.tendsto_slope_zero_left|theorem mul_meas_ge_le_lintegral₀|theorem enorm_integral_le_lintegral_enorm|theorem ENNReal.tsum_geometric|theorem isClosedEmbedding_coe_real|theorem lipschitz_infDist_pt|theorem isClosed_cthickening' mathlib/Mathlib`
- `rg -n 'cmcsd_' over the snapshot project, mathlib and lake-packages-25730c7c/simongmt (no match)`
- `rg -n 'theorem countablyRectifiable_of_measure_zero|theorem GeometricCurrentOn.isOpen_zeroRegion|theorem tsupport_exteriorDerivative_subset' lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `python3 -I scan of runs/20261011T150044Z-ba604216b4/dag.json (961 nodes): frozen types of the selected node and of siblings RET/GC/PF/IMS, accepted reusable declarations (support, mass, IMRep, Lebesgue-derivative lemmas), name collisions for the cmcsd_ prefix (none)`
- `git show ae810e9b / 7a706164 / ea5c1199 / 6efe397f (accepted proofs of lcmp_imRep_measure_restrict, cmr_abs_apply_le_massOn, cmc_fc_cs_massOn_sub_le, cmcs_smi_lintegral_ofReal_deriv_le)`
- `lean Types.lean (16 stub types elaborate); lean InstCheck.lean (coercions, rfl checks); lean AssemblyAx.lean (selected type from stubs; axioms propext, Classical.choice, Quot.sound + named stubs); lean ReusedCheck.lean (reused proofs, standard axioms); lean Probe3/Probe4.lean (lemma names: measure_sdiff, setIntegral_sdiff, image_eq_zero_of_notMem_tsupport)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/Int.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-9a64d46574/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_skeleton_deformation_decomposition/Types.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_skeleton_deformation_decomposition/AssemblyAx.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_skeleton_deformation_decomposition/ReusedCheck.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace Contract.lean and Submission.lean. Its only deformation-theorem material is the separate, unsolved Ch06 specification (project/GMT/Ch06/Contract.lean, DeformationTheorem with IsLatticeChain/Eucl). Those types are incompatible with Ch07, so nothing there is reusable. Mathlib supplies every tool the child proofs cite: LipschitzOnWith.extend_real/extend_pi (McShane), Monotone.ae_differentiableAt, measurable_deriv, HasDerivAt.tendsto_slope_zero_left, Markov (mul_meas_ge_le_lintegral₀), enorm_integral_le_lintegral_enorm, ENNReal.tsum_geometric, lipschitz_infDist_pt, isClosed_cthickening and Int.isClosedEmbedding_coe_real. SimonGMT supplies countablyRectifiable_of_measure_zero, isOpen_zeroRegion and tsupport_exteriorDerivative_subset. The DAG yields four accepted, reusable declarations with identical types: cmcs_smi_lintegral_ofReal_deriv_le, cmc_fc_cs_massOn_sub_le, cmr_abs_apply_le_massOn and lcmp_imRep_measure_restrict. Their proofs recompile with standard axioms. The prefix cmcsd_ has no match anywhere. All child types elaborate, and the assembly of the selected frozen type from the sibling and child types compiles with only propext, Classical.choice and Quot.sound beyond the named stubs.
