# Sharp log-Sobolev inequality on finite cyclic groups

This repository uses Lean and Comparator to verify the sharp log-Sobolev inequality in Theorem 1 of:

> [Xinyuan Xie](https://xinyuanxie-hub.github.io/) and [Haonan Zhang](https://sites.google.com/view/haonanzhangmathsearch-console),
> *Sharp log-Sobolev inequalities and quartic stability on finite cyclic groups*,
> [arXiv:2606.02847](https://arxiv.org/abs/2606.02847).

## Mathematical statement

Let $`\mathbb{Z}_n=\mathbb{Z}/n\mathbb{Z}`$ be the cyclic group equipped with the uniform probability measure $`\pi`$, so that $`\pi(g)=\frac{1}{n}\sum_{x\in\mathbb{Z}_n}g(x)`$. For every $`n\geq 4`$ and every nonnegative $`f:\mathbb{Z}_n\to\mathbb{R}`$,

```math
\mathrm{Ent}_{\pi}(f^2)\leq 2\mathcal{E}_n(f).
```

Here $`\mathrm{Ent}_{\pi}(g)=\pi(g\log g)-\pi(g)\log\pi(g)`$ for nonnegative $`g`$, with natural logarithms and $`0\log 0=0`$, and the Dirichlet form is

```math
\mathcal{E}_n(f)=\sum_{k=0}^{n-1}\min(k,n-k)\,|\widehat f(k)|^2,
```

where

```math
\widehat f(k)=\frac{1}{n}\sum_{x=0}^{n-1}f(x)e^{-2\pi i kx/n}.
```

The constant $`2`$ is sharp by the standard perturbation argument recalled in [Section 5 of the paper](https://arxiv.org/html/2606.02847#S5); the formalization here concerns the inequality.

## Verification

First, we translate the mathematical statement into [Lean](https://lean-lang.org/doc/reference/4.35.0/), a language in which a computer can check mathematical proofs; the statement and its definitions are stored in [Challenge.lean](Challenge.lean). The proof in [Solution.lean](Solution.lean) is generated based on the argument in the paper. We then run [`lake comparator`](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/), which is included in the Lean toolchain, to check this proof against the statement in `Challenge.lean`.

Comparator checks that the theorem statement and its referenced definitions agree on both sides, and that the proof uses only the standard axioms permitted in [comparator.json](comparator.json). It checks the proof with Lean's kernel (its proof checker) and two independent checkers, NanoDa and con-ron. Whether the translation in `Challenge.lean` expresses the intended mathematical statement remains for us to check.

### Check the verification results

1. Sign in to GitHub and open [Lean CI](https://github.com/XinyuanXie-hub/cyclic-lsi-new/actions/workflows/lean.yml). Select a completed run for the version you want to check.
2. Click **Verify the Challenge against Solution**, then expand **Run Comparator with Lean, NanoDa, and con-ron**.
3. Confirm that the job succeeded and its log says `Your solution is okay!`: all three checkers accepted the proof.

### Run the verification independently

1. Click [Fork](https://github.com/XinyuanXie-hub/cyclic-lsi-new/fork) → **Create fork**. In your fork, open **Actions** and enable workflows if prompted.
2. Select **Lean CI → Run workflow**, keep **Branch: main**, and click **Run workflow**.
3. Once it finishes, open the new run in your fork and follow steps 2–3 under [Check the verification results](#check-the-verification-results).

[verify-comparator.sh](scripts/verify-comparator.sh) runs Comparator with all three checkers; [lean.yml](.github/workflows/lean.yml) configures GitHub to build the project and run that script.
