# Sharp log-Sobolev inequality on finite cyclic groups

This project uses [Lean](https://lean-lang.org/), a programming language in which a computer can verify mathematical proofs, to verify the sharp log-Sobolev inequality in Theorem 1 of:

> Xinyuan Xie and Haonan Zhang,
> *Sharp log-Sobolev inequalities and quartic stability on finite cyclic groups*,
> [arXiv:2606.02847](https://arxiv.org/abs/2606.02847).


*The hot spot $`\rho_0`$ at the origin spreads along the finite cycle, according to the long-range transportation specified by the word-length Laplacian $`-A_{\psi_n}`$, until all nodes reach the same temperature.*
<p align="center">
  <a href="assets/word-length-semigroup.png">
    <img src="assets/word-length-semigroup.gif" width="900" alt="Heat initially concentrated at the origin spreads on discrete cycles with n = 5 and n = 21.">
  </a>
</p>


```math
R_n(t)=\frac{\mathrm{Ent}_{\pi}(\rho_t)}{\mathcal E_n(\sqrt{\rho_t})}.
```

<p align="center">
  <a href="assets/entropy-energy-ratio.png">
    <img src="assets/entropy-energy-ratio.gif" width="580" alt="The entropy-to-energy ratios R_n(t) for n = 5 and n = 21 approach 2 from below.">
  </a>
</p>

Here $`\rho_t`$ is the heat density evolving from $`\rho_0`$ at time $`t`$. $`\mathrm{Ent}_{\pi}(\rho_t)`$ and $`\mathcal E_n(\sqrt{\rho_t})`$ are the relative entropy and the Dirichlet form, capturing how $`\rho_t`$ varies from equilibrium information-theoretically and analytically. One may notice that the plotted ratios of these two quantities approach $`2`$ from below, and may wonder whether this upper bound always holds. The inequality we verify below proves this upper bound holds for arbitrary density functions for all $`n \geq 4`$.

## Mathematical statement

Let $`\mathbb Z_n=\mathbb Z/n\mathbb Z`$ be equipped with the uniform probability measure $`\pi`$. The word-length Laplacian and its Dirichlet form are

```math
\begin{aligned}
A_{\psi_n}f(x)&=\sum_{k=0}^{n-1}\min(k,n-k)\widehat f(k)e^{2\pi i kx/n},\\
\mathcal E_n(f)&=\pi(\overline f\,A_{\psi_n}f),
\end{aligned}
```

where $`\widehat f(k)=\frac1n\sum_{x\in\mathbb Z_n}f(x)e^{-2\pi i kx/n}`$ is the Fourier transform of $`f`$ and $`\pi(g)=\frac1n\sum_{x\in\mathbb Z_n}g(x)`$ denotes the average of $`g`$.

For $`g\ge0`$, denote by $`\mathrm{Ent}_\pi(g)=\pi(g\,\log\,g)-\pi(g)\,\log\,\pi(g)`$ the relative entropy of $`g`$, with $`\log`$ denoting the natural logarithm and $`0\,\log\,0=0`$.

<a name="theorem-1"></a>

**Theorem 1.** For every $`n\geq4`$ and every nonnegative $`f:\mathbb Z_n\to\mathbb R`$,

```math
\mathrm{Ent}_\pi(f^2)\leq2\mathcal E_n(f).\qquad(1)
```

Sharpness of the constant $`2`$ follows from a standard perturbation argument (see [Section 5](https://arxiv.org/html/2606.02847#S5)), and we only formalize the inequality part here.

## Verification
<!--
The verification is done by [`lake comparator`](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#comparator), a command in the Lean toolchain that compiles [Challenge.lean](Challenge.lean) and [Solution.lean](Solution.lean) independently and checks whether the proof in the latter proves the theorem stated in the former using the axioms allowed in [`comparator.json`](comparator.json).
-->
To verify the correctness of the inequality in Lean, one only needs to check that the statement and definitions in [Challenge.lean](Challenge.lean) match [Theorem 1](#theorem-1) stated above, <!--review the configuration in [`comparator.json`](comparator.json),--> and confirm that `lake comparator` succeeds.

The results of `lake comparator` can be checked through the GitHub workflow provided by this project as follows:

1. Sign in to GitHub, open the “Actions” tab, then open the first workflow run listed there, or open it directly from [here](https://xinyuanxie-hub.github.io/cyclic-lsi-new/latest-run/).
2. Click “Verify the Challenge against Solution”, then expand “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the log (lines 50–57) reports acceptance by con-ron, NanoDa, and Lean, followed by `Your solution is okay!`.


Note: Here, we use the [“gold standard”](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) for validating proofs in Lean, and we refer readers to [“Challenges and External Checkers”](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) for details on how it works.

<!--
**You can also run `lake comparator` in your own fork through GitHub Actions:**

1. Click “[Fork](https://github.com/XinyuanXie-hub/cyclic-lsi-new/fork)” → “Create fork”. In your fork, open “Actions” and enable workflows.
2. Select “Lean CI” → “Run workflow”, keep “Branch: main”, and click “Run workflow”.
3. Once it finishes, open the new run in your fork and follow steps 2–3 of the first list.


Note: the GitHub workflow is defined in [lean.yml](.github/workflows/lean.yml), which configures GitHub to run [verify-comparator.sh](scripts/verify-comparator.sh), a script that runs Comparator with all three checkers: con-ron, NanoDa, and Lean.

-->
