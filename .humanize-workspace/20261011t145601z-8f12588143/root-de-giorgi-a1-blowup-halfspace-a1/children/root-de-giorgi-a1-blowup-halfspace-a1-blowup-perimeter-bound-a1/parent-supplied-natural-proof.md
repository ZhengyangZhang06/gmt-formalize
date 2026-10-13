# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.blowup_halfspace-a1`
- Child DAG node: `root.de_giorgi-a1.blowup_halfspace-a1.blowup_perimeter_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Selected-node proof, Step 2(a): "If |g| ≤ 1 everywhere, then, as |ν| = 1 μ-a.e., ∫_{E_r} div g ≤ (rⁿ)⁻¹ μ(B_{rR}(x)) ≤ (rⁿ)⁻¹ C(rR)ⁿ = CRⁿ", with C replaced by max(C, 0) as in Step 1. This is Part 3a of the De Giorgi proof: the perimeter bound that feeds Simon's compactness step (Simon, Ch. 3, proof of Theorem 4.3, chapter-03.txt lines 653-656, using the mass bound (6)). The blow-up identity of the selected node's sibling blowup_identity enters here as hypothesis (I), already restricted to fields supported in B_R(0) with rR < ρ₁; the mass bound of the sibling density_estimates enters as hypothesis (M). No sibling child of this split is used.

Notation. η := blowUpMap x r, η(y) = r⁻¹·(y − x); div := euclideanDivergence; B_ρ(z) is the open ball; ⟨·,·⟩ is the Euclidean inner product.

1. Fix r > 0 and R > 0 with rR < ρ₁, and g C¹ with compact support, tsupport g ⊆ B_R(0) and |g(y)| ≤ 1 for all y. Put ρ := rR, so ρ ∈ (0, ρ₁), and B := B_ρ(x). By (M), μ(B) ≤ ENNReal.ofReal(Cρⁿ) < ∞.

2. (g∘η vanishes off B.) If y ∉ B then |y − x| ≥ ρ = rR, so |η(y)| = r⁻¹|y − x| ≥ R and η(y) ∉ B_R(0); as tsupport g ⊆ B_R(0), η(y) ∉ tsupport g and g(η(y)) = 0.

3. Put h(y) := ⟨g(η(y)), ν(y)⟩. For μ-a.e. y, namely every y with |ν(y)| = 1, |h(y)| ≤ 1_B(y): for y ∈ B, Cauchy-Schwarz gives |h(y)| ≤ |g(η(y))|·|ν(y)| ≤ 1·1; for y ∉ B, h(y) = 0 by step 2.

4. The indicator 1_B is μ-integrable because μ(B) < ∞, and ∫1_B dμ = μ(B) (as a real number). The norm of a Bochner integral is at most the integral of any integrable a.e. dominating function, so |∫h dμ| ≤ μ(B). (This holds even if h is not integrable, since its Bochner integral is then 0 by convention.)

5. From μ(B) ≤ ENNReal.ofReal(Cρⁿ) we get μ(B) ≤ max(Cρⁿ, 0) as real numbers, and max(Cρⁿ, 0) ≤ max(C, 0)·ρⁿ because ρⁿ > 0 (equality if C ≥ 0; if C < 0 the left side is 0 ≤ the right side).

6. By (I) applied to (r, R, g): ∫_{η(E)} div g = −(rⁿ)⁻¹∫h dμ ≤ (rⁿ)⁻¹|∫h dμ| ≤ (rⁿ)⁻¹·max(C, 0)·(rR)ⁿ = max(C, 0)·Rⁿ, using (rⁿ)⁻¹ > 0, steps 4-5 and (rR)ⁿ = rⁿRⁿ. ∎

## Key steps

1. ρ := rR ∈ (0, ρ₁), so μ(B_ρ(x)) ≤ Cρⁿ < ∞ by (M).
2. g∘η vanishes off B_ρ(x), so |⟨g∘η, ν⟩| ≤ 1_{B_ρ(x)} μ-a.e. (|g| ≤ 1, |ν| = 1).
3. |∫⟨g∘η, ν⟩dμ| ≤ μ(B_ρ(x)) ≤ max(C, 0)ρⁿ.
4. By (I), ∫_{η(E)} div g = −(rⁿ)⁻¹∫⟨g∘η, ν⟩dμ ≤ (rⁿ)⁻¹max(C, 0)(rR)ⁿ = max(C, 0)Rⁿ.

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
