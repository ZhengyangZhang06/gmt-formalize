# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.blowup_halfspace-a1`
- Child DAG node: `root.de_giorgi-a1.blowup_halfspace-a1.l1loc_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Selected-node proof, Step 4: "For a bounded Borel f vanishing outside a compact K: |∫_{F_{φ(k)}} f − ∫_G f| ≤ sup|f|·L^N(K ∩ (F_{φ(k)} Δ G)) → 0" and, in (P), "|L^N(G ∩ B_R(0)) − L^N(F_{φ(k)} ∩ B_R(0))| ≤ L^N(K ∩ (F_{φ(k)} Δ G)) → 0 and likewise for B_R(0) ∖ G"; in Simon, Ch. 3, proof of Theorem 4.3, this is the passage from χ_{ρ_k⁻¹E} → χ_F in L¹_loc to (7) (chapter-03.txt lines 653-660). No sibling child is used. The parent's Step 4 is phrased for bounded Borel f vanishing outside a compact set. This child is stated for continuous compactly supported f, which is all the selected node needs: it applies (i) only to f = D_vζ = fderiv ℝ ζ · v with ζ ∈ C¹_c, which is continuous with compact support. It applies (ii) to the open balls B = B_R(0).

Notation. L^N := volume on ℝ^N; for compact K, d_k(K) := L^N(K ∩ (F_k Δ G)) ∈ [0, ∞]; hypothesis (L): d_k(K) → 0 for every compact K. Integrals over a set S are integrals with respect to L^N restricted to S.

1. (Integrals: set-up.) Let f be continuous with compact support and K := tsupport f, a compact set; L^N(K) < ∞. A continuous function with compact support is bounded, so fix M ≥ 0 with |f(y)| ≤ M for all y; f is L^N-integrable.

2. For a null-measurable set S, ∫_S f = ∫ 1_S·f (integral of the indicator function), and 1_S·f is integrable because f is. Hence ∫_{F_k} f − ∫_G f = ∫ (1_{F_k} − 1_G)·f.

3. Pointwise, |(1_{F_k}(y) − 1_G(y))·f(y)| ≤ M·1_{K ∩ (F_k Δ G)}(y) for every y: if y ∉ F_k Δ G the left side is 0; if y ∉ K then f(y) = 0; otherwise the left side is |f(y)| ≤ M.

4. The set K ∩ (F_k Δ G) is null-measurable (K is closed, and symmetric differences of null-measurable sets are null-measurable) and has finite measure d_k(K) ≤ L^N(K) < ∞; so M·1_{K ∩ (F_k Δ G)} is integrable with integral M·d_k(K) (d_k(K) read as a real number). By step 3 and the monotonicity of the norm of the integral, |∫_{F_k} f − ∫_G f| ≤ M·d_k(K).

5. By (L), d_k(K) → 0 in [0, ∞]; since all d_k(K) are finite and the real-part map [0, ∞) → ℝ is continuous at 0, the real numbers d_k(K) tend to 0, hence M·d_k(K) → 0. By the squeeze theorem ∫_{F_k} f → ∫_G f. This proves (i).

6. (Volumes: set-up.) Let B be bounded and K := closure of B. K is closed and bounded in ℝ^N, hence compact, B ⊆ K and L^N(K) < ∞. Put a := L^N(G ∩ B) ≤ L^N(K) < ∞ and d_k := d_k(K), so d_k → 0 by (L).

7. F_k ∩ B ⊆ (G ∩ B) ∪ (K ∩ (F_k Δ G)): a point of F_k ∩ B outside G lies in F_k ∖ G ⊆ F_k Δ G and in B ⊆ K. By monotonicity and subadditivity of the (outer) measure, L^N(F_k ∩ B) ≤ a + d_k. Symmetrically G ∩ B ⊆ (F_k ∩ B) ∪ (K ∩ (F_k Δ G)), so a ≤ L^N(F_k ∩ B) + d_k, i.e. a − d_k ≤ L^N(F_k ∩ B) with truncated subtraction in [0, ∞].

8. As d_k → 0 and a < ∞, a + d_k → a and a − d_k → a − 0 = a (addition is continuous on [0, ∞], and truncated subtraction is continuous at a pair whose first entry is finite). The squeeze theorem in [0, ∞] gives L^N(F_k ∩ B) → a = L^N(G ∩ B).

9. Likewise B ∖ F_k ⊆ (B ∖ G) ∪ (K ∩ (F_k Δ G)) (a point of B ∖ F_k lying in G is in G ∖ F_k ⊆ F_k Δ G) and B ∖ G ⊆ (B ∖ F_k) ∪ (K ∩ (F_k Δ G)), with L^N(B ∖ G) ≤ L^N(K) < ∞. The argument of steps 7-8 gives L^N(B ∖ F_k) → L^N(B ∖ G). No measurability of B was used. This proves (ii). ∎

## Key steps

1. f ∈ C_c is integrable, bounded by M and vanishes off the compact K = tsupport f.
2. ∫_{F_k} f − ∫_G f = ∫(1_{F_k} − 1_G)f, dominated by M·1_{K∩(F_kΔG)}, so |∫_{F_k} f − ∫_G f| ≤ M·L^N(K ∩ (F_kΔG)) → 0.
3. For bounded B, K = closure B is compact and two-sided inclusions give L^N(G∩B) − d_k ≤ L^N(F_k∩B) ≤ L^N(G∩B) + d_k with L^N(G∩B) < ∞.
4. Squeeze in [0, ∞]; the same for B ∖ F_k versus B ∖ G.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `rg -n "theorem tendsto_of_subseq_tendsto|theorem addHaar_image_homothety|theorem addHaar_smul|theorem addHaar_preimage_smul|theorem addHaar_image_continuousLinearEquiv|theorem integral_indicator₀|theorem setIntegral_union" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem HasCompactSupport.fderiv_apply" <snapshot>/mathlib/Mathlib; rg -n "mul_le_mul_left'|theorem mul_le_mul_right|zero_le" <snapshot>/mathlib/Mathlib/Algebra/Order`
- `rg -n "theorem trace_smulRight|trace_smulRight" <snapshot>/mathlib/Mathlib`
- `rg -n "symmDiff" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral; rg -n "theorem tendsto_measure_symmDiff|measure_symmDiff_le" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem [A-Za-z_']*blowUp|lemma [A-Za-z_']*blowUp" .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n "volume \(blowUpMap" .lake/packages/simongmt/Poincare/SimonGMT; rg -n "euclideanDivergence_smul|smulRight" .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `rg -n "^theorem|^lemma|^def" .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `python3 -I dag.json scan: lean_statements containing blowUpMap/symmDiff; lean_name collision check (152 nodes, also case-insensitive)`
- `python3 -I (importlib of verifier/gmt-compare.py) contract_scope + child_modules(contract mode) -> GMT/Scratch/BHS_Challenge_<key>.lean; lake env lean on BHS_Challenge_*.lean, BHS_Proof_*.lean, BHS_FullCheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-chart-blowup-tangent-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_FullCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_blowup_image_volume.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_l1loc_transfer.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_blowup_perimeter_bound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_blowup_flatness.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c). No Mathlib, SimonGMT or accepted-DAG declaration states any of the four children. Mathlib supplies only ingredients: addHaar_smul, NullMeasurableSet.const_smul, measure_preimage_add_right, integral_indicator₀, LinearMap.trace_smulRight (Trace.lean:272), HasCompactSupport.fderiv_apply (𝕜 explicit), measure_symmDiff_le, and tendsto_of_subseq_tendsto (CountablyGenerated.lean:125), which handles Step 6 directly. SimonGMT has blowUpMap (Rectifiable.lean) and euclideanDivergence/euclideanDivergence_eq_sum_inner (BV.lean). Its blow-up scaling lemmas are for μHE[n] and closed balls, in Chapter04 (not imported by Submission). FinitePerimeter.lean has definitions only. The rg searches for a Lebesgue-volume blow-up lemma, a divergence-of-ζv lemma and a set-integral/symmDiff transfer lemma found nothing. The accepted DAG nodes setIntegral_blowUpMap_image and chartTD_setIntegral_blowUpMap_image are μHE[n] identities with different types. All four child types elaborate in the exact NodeChallenge scope, and their full proofs compile with only propext, Classical.choice and Quot.sound. The selected-node assembly compiles against the frozen sibling types. No proposed lean_name collides with dag.json.
