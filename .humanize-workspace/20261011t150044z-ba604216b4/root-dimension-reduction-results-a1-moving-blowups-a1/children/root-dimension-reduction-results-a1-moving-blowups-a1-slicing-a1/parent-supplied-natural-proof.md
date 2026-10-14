# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.slicing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 6.4.6–4.11 (4.8–4.9 are printed for f∈C¹, via 4.11, with the instruction to use f^{(σ)} and let σ↓0; that limit is done in step 3). Restrictions are taken w.r.t. the given representations (μ,ξ) of T and (μ',ξ') of ∂T (Simon 2.9): A_t=T⌞{f<t}, B_t=(∂T)⌞{f<t}, Z_t=∂A_t−B_t=⟨T,f,t₋⟩.
Notation: |α|:=covectorEuclideanNorm α, |ω|_∞:=sup_x|ω(x)|. (E1) |β∧γ|≤|β||γ| for a 1-covector β and a k-covector γ: k!|γ|²=Σ_{i_1,…,i_k}γ(e_{i_1},…,e_{i_k})² is the basis-independent Hilbert–Schmidt norm of γ, so |·| is invariant under orthogonal coordinate changes; rotate so that β=|β|e¹, then β∧γ=|β|Σ_{I∌1}γ_Ie¹∧e^I has norm ≤|β||γ|. (E2) By hypothesis |ξ(x)(α)|≤|α| μ-a.e. and |ξ'(x)(α)|≤|α| μ'-a.e.
1. (Restricted currents.) For Borel E and ω∈𝒟^{k+1}(U) let A_E(ω):=∫_Eξ(x)(ω(x))dμ(x). The integrand is a.e. strongly measurable (ξ composed with the continuous pairing) and by (E2) bounded μ-a.e. by |ω|_∞1_{tsupport ω}, with μ(tsupport ω)<∞ (compact in U); so it is integrable, and A_E is linear. If ω_j→0 in 𝒟^{k+1}(U) (TestFormOnConverges: supports in a fixed compact K⊆U, uniform convergence of the forms and all derivatives; |·| is equivalent to any norm on covectors), |A_E(ω_j)|≤|ω_j|_∞μ(K)→0, so A_E∈𝒟_{k+1}(U). Likewise B_E(η):=∫_Eξ'(η)dμ' gives B_E∈𝒟_k(U). A_t:=A_{{f<t}}, B_t:=B_{{f<t}} ({f<t} is open, f being continuous) satisfy the first two conclusions; T=A_{ℝ^P}, ∂T=B_{ℝ^P} by the representation hypotheses.
2. (Support.) Let η∈𝒟^k(U), K:=tsupport η disjoint from {f=t}. K₋:=K∩{f<t}, K₊:=K∩{f>t} are disjoint compact sets with union K. Take χ∈C^∞(ℝ^P;[0,1]) with χ=1 near K₋, χ=0 near K₊; η₋:=χη, η₊:=(1−χ)η are test forms in U, η=η₋+η₊, and tsupport η_±⊆K_± (η_± vanishes near K_∓ and off K). As η₊, dη₊ vanish on {f<t}, (∂A_t)(η₊)=A_t(dη₊)=∫_{f<t}ξ(dη₊)dμ=0 and B_t(η₊)=∫_{f<t}ξ'(η₊)dμ'=0. As η₋, dη₋ vanish off {f<t}, (∂A_t)(η₋)=∫_{f<t}ξ(dη₋)dμ=∫ξ(dη₋)dμ=T(dη₋)=∂T(η₋)=∫ξ'(η₋)dμ'=∫_{f<t}ξ'(η₋)dμ'=B_t(η₋). Adding gives (A_t).boundary η=B_t η, the third conclusion.
3. (Pointwise bound; Simon 4.9 for Lipschitz f.) Fix t, open W, 0<h<1, ε:=h²/8. Take C^∞ nonincreasing γ:ℝ→[0,1] with γ=1 on (−∞,t−h+ε], γ=0 on [t−ε,∞), |γ'|≤1/(h−4ε) (mollify at scale <ε the piecewise linear function equal to 1 on (−∞,t−h+2ε], 0 on [t−2ε,∞), linear between). f_σ:=f∗φ_σ (φ_σ a standard mollifier) is C^∞, |∇f_σ|≤L, |f_σ−f|≤Lσ. For Lσ<ε let g_σ:=γ∘f_σ (C^∞, [0,1]-valued, derivatives bounded on compacts), g:=γ∘f (continuous).
(i) For η∈𝒟^k(U), g_σdη and g_ση are test forms in U and d(g_ση)=dg_σ∧η+g_σdη, so T(g_σdη)−∂T(g_ση)=T(g_σdη)−T(d(g_ση))=−T(dg_σ∧η).
(ii) dg_σ=γ'(f_σ)df_σ vanishes unless t−h+ε<f_σ<t−ε, which forces t−h<f<t (as |f_σ−f|<ε); |dg_σ|≤L/(h−4ε). By the representation of T, (E1), (E2): if tsupport η⊆W, |η|≤1, then |T(dg_σ∧η)|≤∫|dg_σ||η|dμ≤(L/(h−4ε))μ(W∩{t−h<f<t}).
(iii) As σ↓0, g_σ→g uniformly (γ Lipschitz, f_σ→f uniformly), so T(g_σdη)→∫gξ(dη)dμ and ∂T(g_ση)→∫gξ'(η)dμ' (dominated convergence on the compact tsupport η, of finite μ- and μ'-measure). So, writing g_h:=γ_h∘f to record the dependence on h, and as h−4ε=h(1−h/2), for admissible η (tsupport η⊆W, |η|≤1):
 ∫g_hξ(dη)dμ − ∫g_hξ'(η)dμ' ≤ (L/(h(1−h/2)))μ(W∩{t−h<f<t}).
(iv) As h↓0, g_h→1_{{f<t}} pointwise (if f(x)<t, then f(x)≤t−h+ε once h≤t−f(x), so g_h(x)=1; if f(x)≥t, then f(x)≥t−ε and g_h(x)=0). By dominated convergence ∫g_hξ(dη)dμ→∫_{f<t}ξ(dη)dμ=(∂A_t)(η) and ∫g_hξ'(η)dμ'→B_t(η). Along h_i↓0 realizing liminf_{h↓0}h⁻¹μ(W∩{t−h<f<t}), with (1−h/2)⁻¹→1, this gives Z_t(η)=(∂A_t−B_t)(η)≤L·liminf_{h↓0}h⁻¹μ(W∩{t−h<f<t}) for admissible η, so M_W(Z_t)=sup ofReal(Z_t(η))≤L·liminf_{h→0⁺}ofReal(h⁻¹)μ(W∩{t−h<f<t}) in [0,∞], the fourth conclusion. (Read (ii)–(iv) in [0,∞]; the integrals are finite since only tsupport η matters, e.g. μ(tsupport η∩{t−h<f<t})<∞ may replace μ(W∩{t−h<f<t}) in (ii). If L=0, f is constant, {t−h<f<t}=∅ for small h, the bound in (ii) is 0 and Z_t=0, so 0·∞=0 is harmless; if the liminf is ∞, then L>0 and the claim is trivial.)
4. (Integral bound; Simon 4.10.) Fix open W and a, b. If a≥b, Ioo a b=∅ and there is nothing to prove; let a<b. If L=0, M_W(Z_t)=0 for all t (step 3). If L>0 and μ(W∩{a<f<b})=∞ there is nothing to prove. Otherwise F(s):=μ(W∩{a<f<s}) for s≤b, F(s):=F(b) for s>b, is real, bounded, nondecreasing, F=0 on (−∞,a]. For t∈(a,b), 0<h<t−a, {t−h<f<t}⊆{a<f<t}∖{a<f<t−h}, so μ(W∩{t−h<f<t})≤F(t)−F(t−h). F is differentiable a.e. (Lebesgue, Monotone.ae_differentiableAt), and there step 3 gives M_W(Z_t)≤LF'(t). By lintegral_mono_ae (no measurability of t↦M_W(Z_t) needed for the lower integral), ∫⁻_{(a,b)}M_W(Z_t)dt≤L∫⁻_{(a,b)}F'(t)dt. Finally ∫_{(a,b)}F'≤F(b)−F(a)=μ(W∩{a<f<b}) (F(a)=0) by MonotoneOn.intervalIntegral_deriv_mem_uIcc: F'=deriv F≥0 a.e. is integrable on [a,b] (MonotoneOn.intervalIntegrable_deriv) with interval integral in [0,F(b)−F(a)]. This is the fifth conclusion.

## Key steps

1. Restricted currents A_t, B_t exist: integrable integrands, continuity as μ, μ' are finite on compacts.
2. Support: split η into parts supported in {f<t} and {f>t}; ∂A_t and B_t agree on each.
3. Pointwise bound: cut-offs γ∘f_σ give T(g_σdη)−∂T(g_ση)=−T(dg_σ∧η), at most L/(h−4ε)·μ(W∩{t−h<f<t}); let σ↓0, then h↓0.
4. Integral bound: pointwise bound ≤LF'(t) for monotone F(s)=μ(W∩{a<f<s}); integrate, ∫F'≤F(b)−F(a).

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean`
- `python3 scans of RUN/dag.json: selected node, prerequisite types, accepted reusable declarations and their lean_statement, status of the children of root.compactness_of_minimizing_currents-a1, lean_name collisions (dimred_mbl_: no match)`
- `grep -n _existing_lean_name_problem _accepted_checkpoint contract in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py and speculation.py`
- `grep -rn of every cited Mathlib/SimonGMT lemma name in the pinned lake packages`
- `lean (v4.35.0-rc3) on AllTypes.lean, AssemblyCond.lean (#print axioms) and 12 Challenge_<key>.lean modules; lean_contract.validate_lean_statement on all child types`
- `sed -n on book/chapter-06.txt (2.15, 2.23–2.33, 3.3–3.10, 4.6–4.11) and book/chapter-07.txt (7.2.4–7.2.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/mb2/lean/src/AssemblyCond.lean`

Pins match (HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b366308) and Submission.lean is byte-identical to the frozen contract. The pinned libraries lack Federer–Fleming compactness, the deformation theorem, flat convergence, Lipschitz slicing and integral push-forward by nonlinear maps; SimonGMT supplies currents, mass, support, weak convergence, affine push-forward, the Lipschitz area formula and approximate tangent spaces, and every cited library name exists. Accepted declarations with exact types: dtc_vanish_off_support and dor_imrep_massOn_eq_measure_and_support (reused). The children of root.compactness_of_minimizing_currents-a1 are decomposing, not accepted, so they cannot be shared; identical types with unique dimred_mbl_* names are used. A child's prerequisites are its children plus depends_on, so monotonicity enters as a hypothesis. All 12 child types elaborate and the conditional assembly proves the parent type (axioms propext, Classical.choice, Quot.sound).
