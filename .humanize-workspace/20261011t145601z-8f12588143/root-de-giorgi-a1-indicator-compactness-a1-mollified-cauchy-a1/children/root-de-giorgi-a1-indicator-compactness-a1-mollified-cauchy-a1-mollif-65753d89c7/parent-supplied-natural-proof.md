# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.indicator_compactness-a1.mollified_cauchy-a1`
- Child DAG node: `root.de_giorgi-a1.indicator_compactness-a1.mollified_cauchy-a1.mollifier_l1_error-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Step 2 (the mollification-error claim) of the parent's supplied proof. That claim is Step 3 of the grandparent's proof of Simon, Ch. 2, Theorem 2.6 (chapter-02.txt lines 598–620; the printed proof refers the mollification/Arzelà argument to [GT01, Thm 7.22]). Here the kernel ρ, the scale σ and the translation range |h| ≤ σ are general. The parent's Step 0 (WLOG measurable) is carried out for the single set F.

Notation.
- χ := 1_F : ℝ^N → ℝ.
- v(y) := ∫_F ρ(y − z) dz, the integral with respect to L^N⌞F.
- S_h := {y : y + h ∈ S} for a set S and h ∈ ℝ^N.
- B_R := B_R(0), the open ball; it is empty when R ≤ 0.
- ∫⁻ is the [0, ∞]-valued Lebesgue integral, and ofReal(t) := max(t, 0).

1. (Reduction to measurable F.) Let F' be the measurable hull of F (Mathlib toMeasurable). It is a Borel set with F ⊆ F', and F' = F up to an L^N-null set because F is null-measurable.
 (a) L^N⌞F' = L^N⌞F. Hence ∫_{F'} ρ(y − z) dz = v(y) for every y.
 (b) 1_{F'} = 1_F L^N-a.e., hence also (L^N⌞B_R)-a.e. So the integrand of the conclusion changes only on a null set, and its ∫⁻ over B_R is unchanged.
 (c) Fix h. The translation y ↦ y + h preserves L^N, so preimages of a.e.-equal sets are a.e.-equal: F'_h = F_h a.e. Hence B_R ∩ (F'_h Δ F') = B_R ∩ (F_h Δ F) a.e. The two sets have the same measure, so the translation hypothesis holds for F'.
 By (a)–(c), it suffices to prove the claim for F'. From now on assume F is a Borel set, so χ is Borel measurable with values in {0, 1}.

2. (Kernel facts.)
 - ρ is continuous with compact support, hence Borel measurable and integrable.
 - If ρ(h) ≠ 0, then h ∈ support ρ ⊆ B̄_σ(0), so |h| ≤ σ.

3. (Pointwise representation.) Fix y ∈ ℝ^N.
 (a) Since F is measurable, v(y) = ∫ χ(z)ρ(y − z) dz. The map z ↦ y − z preserves L^N, being a reflection followed by a translation. Substituting h = y − z gives v(y) = ∫ ρ(h)χ(y − h) dh.
 (b) h ↦ ρ(h)χ(y − h) is measurable with |ρ(h)χ(y − h)| ≤ ρ(h), hence integrable. Also ∫ ρ(h)χ(y) dh = χ(y)·∫ρ = χ(y).
 (c) Subtracting these two integrable integrands, v(y) − χ(y) = ∫ ρ(h)(χ(y − h) − χ(y)) dh. Since ρ ≥ 0,
 |v(y) − χ(y)| ≤ ∫ |ρ(h)(χ(y − h) − χ(y))| dh = ∫ ρ(h)|χ(y − h) − χ(y)| dh.
 (d) The last integrand is nonnegative and integrable, being bounded by ρ because |χ(y − h) − χ(y)| ≤ 1. So ofReal of its integral equals ∫⁻ ofReal(ρ(h)|χ(y − h) − χ(y)|) dh. Since ρ(h) ≥ 0, this equals ∫⁻ ofReal(ρ(h))·ofReal|χ(y − h) − χ(y)| dh. As ofReal is monotone,
 (∗) ofReal|v(y) − χ(y)| ≤ ∫⁻ ofReal(ρ(h))·ofReal|χ(y − h) − χ(y)| dh.

4. (Tonelli.) Put G(y, h) := ofReal(ρ(h))·ofReal|χ(y − h) − χ(y)|. G is a Borel measurable [0, ∞]-valued function on ℝ^N × ℝ^N, because (y, h) ↦ y − h is continuous and ρ, χ are Borel. Integrate (∗) over B_R. Tonelli's theorem for the σ-finite measures L^N⌞B_R and L^N exchanges the order:
 ∫⁻_{B_R} ofReal|v − χ| dy ≤ ∫⁻_{y ∈ B_R} ∫⁻_h G(y, h) dh dy = ∫⁻_h (∫⁻_{y ∈ B_R} G(y, h) dy) dh.

5. (Inner integral.) Fix h. The factor ofReal(ρ(h)) is constant in y and the other factor is measurable in y, so
 ∫⁻_{y ∈ B_R} G(y, h) dy = ofReal(ρ(h))·∫⁻_{B_R} ofReal|χ(y − h) − χ(y)| dy.
 If ρ(h) = 0, this is 0. Assume ρ(h) ≠ 0.
 - |χ(y − h) − χ(y)| equals 1 if exactly one of y − h ∈ F and y ∈ F holds, and 0 otherwise.
 - F_{−h} = {y : y + (−h) ∈ F} = {y : y − h ∈ F}, so ofReal|χ(y − h) − χ(y)| = 1_{F_{−h} Δ F}(y).
 - F_{−h} Δ F is measurable, so the inner integral equals (L^N⌞B_R)(F_{−h} Δ F) = L^N(B_R ∩ (F_{−h} Δ F)).
 - By step 2, |−h| = |h| ≤ σ. The hypothesis at −h gives L^N(B_R ∩ (F_{−h} Δ F)) ≤ ofReal(C|−h|) = ofReal(C|h|) ≤ ofReal(σC). The last inequality uses C ≥ 0 and |h| ≤ σ.
 Hence ∫⁻_{y ∈ B_R} G(y, h) dy ≤ ofReal(ρ(h))·ofReal(σC) for every h. This holds trivially when ρ(h) = 0.

6. (Conclusion.) By steps 4 and 5 and monotonicity of ∫⁻,
 ∫⁻_{B_R} ofReal|v − χ| dy ≤ ∫⁻ ofReal(ρ(h))·ofReal(σC) dh = (∫⁻ ofReal(ρ))·ofReal(σC).
 Since ρ ≥ 0 is integrable, ∫⁻ ofReal(ρ) = ofReal(∫ρ) = ofReal(1) = 1. So the left side is ≤ ofReal(σC). ∎

Lean pointers (Mathlib 25730c7c). A sorry-free Lean proof following exactly these steps compiled during decomposition.
- Step 1: NullMeasurableSet.toMeasurable_ae_eq; setIntegral_congr_set; indicator_ae_eq_of_ae_eq_set; (measurePreserving_add_right volume h).quasiMeasurePreserving.preimage_ae_eq; ae_eq_set_inter; ae_eq_set_symmDiff; measure_congr; lintegral_congr_ae with ae_restrict_of_ae.
- Step 2: Continuous.integrable_of_hasCompactSupport.
- Step 3: integral_indicator; integral_sub_left_eq_self; integral_sub; integral_mul_const; abs_integral_le_integral_abs; ofReal_integral_eq_lintegral_ofReal; ENNReal.ofReal_mul.
- Step 4: lintegral_lintegral_swap.
- Step 5: lintegral_const_mul; lintegral_indicator_one; Measure.restrict_apply; Set.indicator_of_mem and Set.indicator_of_notMem.
- Step 6: lintegral_mul_const; ofReal_integral_eq_lintegral_ofReal.

## Key steps

1. Replace F by its Borel measurable hull F' = F a.e. This leaves v unchanged, the integrand unchanged a.e., and the translation hypothesis unchanged (translations preserve L^N).
2. For each y: v(y) − 1_F(y) = ∫ρ(h)(1_F(y−h) − 1_F(y)) dh, by the substitution h = y − z and ∫ρ = 1. Hence ofReal|v(y) − 1_F(y)| ≤ ∫⁻ ofReal(ρ(h))·ofReal|1_F(y−h) − 1_F(y)| dh.
3. Tonelli for (L^N⌞B_R) × L^N exchanges the order of integration.
4. For each h, the inner integral equals ofReal(ρ(h))·L^N(B_R ∩ (F_{−h} Δ F)). This is ≤ ofReal(ρ(h))·ofReal(σC) by the hypothesis at −h, since ρ(h) ≠ 0 forces |h| ≤ σ, and C ≥ 0.
5. ∫⁻ ofReal ρ = ofReal ∫ρ = 1, so the total is ≤ ofReal(σC).

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean; cat <snapshot>/manifest.json`
- `grep -n 'theorem continuous_convolution_right\|theorem continuous_convolution_left\|HasCompactSupport.continuous_convolution' <snapshot>/mathlib/Mathlib/Analysis/Convolution.lean; grep -n '^theorem convolution_def\|^noncomputable def convolution' (same file)`
- `grep -n "theorem setLIntegral_mono'\|theorem lintegral_add_left'\|theorem lintegral_add_right'\|theorem setLIntegral_const \|theorem lintegral_indicator_one₀\|theorem lintegral_indicator_one \|theorem setLIntegral_mono_ae" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/*.lean`
- `grep -rn 'protected theorem symmDiff' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean; grep -n "theorem restrict_apply'\|theorem restrict_apply \|theorem restrict_apply₀" <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `grep -rn 'theorem integral_sub_left_eq_self\|theorem lintegral_lintegral_swap\|theorem ofReal_integral_eq_lintegral_ofReal\|theorem integral_indicator \|theorem setIntegral_congr_set\|theorem indicator_ae_eq_of_ae_eq_set\|theorem toMeasurable_ae_eq\|theorem preimage_ae_eq\|theorem lintegral_const_mul \|theorem lintegral_mul_const \|theorem locallyIntegrable_const\|theorem lintegral_congr_ae\|theorem ae_eq_set_symmDiff\|theorem norm_integral_le_integral_norm' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `grep -rn 'theorem integral_div_left_eq_self\|theorem measurePreserving_mul_right' <snapshot>/mathlib/Mathlib/MeasureTheory (to_additive sources of integral_sub_left_eq_self, measurePreserving_add_right)`
- `grep -n 'IsLocallyFiniteMeasure (μ.restrict' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean; grep -n 'theorem ae_eq_set_inter' <snapshot>/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean; grep -rn 'indicator_of_notMem' <snapshot>/mathlib/Mathlib/Algebra; grep -rn 'theorem Continuous.integrable_of_hasCompactSupport' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n 'theorem continuous_convolution_right|theorem integral_sub_left_eq_self|...' <snapshot>/mathlib/Mathlib (timed out after 2 min; replaced by the targeted greps above)`
- `grep -rn -i 'mollif\|convolution\|continuous_convolution\|translat' .lake/packages/simongmt/Poincare/SimonGMT --include=*.lean | grep -i 'theorem\|lemma\|def '`
- `python3 -I scope.py GMT/Ch03/Contract.lean (importlib of verifier/gmt-compare.py; contract_scope(text, 'GMT.Ch03.main_theorem'))`
- `python3 -I validate.py stmtA.txt stmtB.txt (importlib of verifier/lean_contract.py; validate_lean_statement)`
- `lake env lean /tmp/mollcauchy-decomp/lean/Challenge_A.lean; Challenge_B.lean; Assembly.lean; ChildProofs.lean; FullCheck.lean; FullCheck2.lean (#print axioms)`
- `python3 -I lean_name/statement collision check over dag.json (168, later 185 nodes); grep -rho "indCompact_[A-Za-z0-9_']*" nodes dag.json issue-workers.json; grep -rl indCompact_mollCauchy nodes issue-workers.json`
- `git show <de-giorgi branches>:GMT/Ch03/Submission.lean | grep -n 'theorem Submission\.' (child declaration convention inside namespace GMT.Ch03)`
- `sed -n 590,632p book/chapter-02.txt; grep -n '2.6 Theorem (Compactness\|GT01, The\|orem 7.22' book/chapter-02.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-mollified-cauchy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-mollified-cauchy-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-mollified-cauchy-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/mollcauchy-decomp/lean/Challenge_A.lean`
- `/tmp/mollcauchy-decomp/lean/Challenge_B.lean`
- `/tmp/mollcauchy-decomp/lean/Assembly.lean`
- `/tmp/mollcauchy-decomp/lean/ChildProofs.lean`
- `/tmp/mollcauchy-decomp/lean/FullCheck2.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c).

What the libraries lack:
- Neither Mathlib nor SimonGMT has an L¹ mollification-error bound derived from translation estimates.
- Neither has a continuity lemma for y ↦ ∫_F ρ(y − z) dz.
- The SimonGMT grep matches only the Chapter08 constancyMollifier and convolution-derivative lemmas.
So both facts become children.

Mathlib provides everything needed to prove them:
- HasCompactSupport.continuous_convolution_right (Convolution.lean:640) with convolution_def, locallyIntegrable_const, and the IsLocallyFiniteMeasure instance for μ.restrict s (Finite.lean:336).
- toMeasurable_ae_eq, setIntegral_congr_set, indicator_ae_eq_of_ae_eq_set, QuasiMeasurePreserving.preimage_ae_eq, ae_eq_set_inter and ae_eq_set_symmDiff.
- integral_indicator, integral_sub_left_eq_self (to_additive of integral_div_left_eq_self), ofReal_integral_eq_lintegral_ofReal and lintegral_lintegral_swap.
- lintegral_const_mul and lintegral_mul_const, lintegral_indicator_one and lintegral_indicator_one₀, Measure.restrict_apply and restrict_apply', NullMeasurableSet.symmDiff, setLIntegral_mono', lintegral_add_left' and lintegral_add_right', setLIntegral_const, and Continuous.integrable_of_hasCompactSupport.

Lean results:
- Both child types elaborate in the exact NodeChallenge scope and pass validate_lean_statement.
- The parent's frozen type is proved from the child stubs with no extra imports.
- Complete proofs of both children compile.
- The combined file proves A, B and the parent through comparator-style `exact Submission.X` targets, with axioms propext, Classical.choice and Quot.sound only.
- Neither lean_name collides with dag.json (185 nodes) or with GMT/.
