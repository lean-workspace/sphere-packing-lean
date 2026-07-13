---
title: 'Cohn-Elkies linear programming bounds'
type: "blueprint-chapter"
tags:
  - "blueprint"
---

In 2003 Cohn and Elkies [@ElkiesCohn]  developed  linear programming bounds that apply directly to sphere packings. The goal of this section is to formalize the Cohn--Elkies linear programming bound.

The following theorem is the key result of [@ElkiesCohn]. (Note that the original theorem is stated for a class of functions more general then Schwartz functions.)

## Theorem: Cohn--Elkies {\cite{ElkiesCohn}} {#thm:Cohn-Elkies-periodic lean="LinearProgrammingBound'" uses="def:Fourier-Transform, SpherePacking.density"}

Let $X\subset\mathbb{R}^d$ be a discrete subset such that $\|x-y\|\geq 1$ for any distinct $x,y\in X$. Suppose that $X$ is $\Lambda$-periodic with respect to some lattice $\Lambda\subset\mathbb{R}^d$. Let $f:\mathbb{R}^d\to\mathbb{R}$ be a Schwartz function that is not identically zero and satisfies the following conditions:

$$
\begin{equation*}f(x)\leq 0\mbox{ for } \|x\|\geq 1\end{equation*}
$$
 and

$$
\begin{equation*}\widehat{f}(x)\geq0\mbox{ for all } x\in\mathbb{R}^d.\end{equation*}
$$

  Then the density of any $\Lambda$-periodic sphere packing is bounded above by 
$$
\frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).
$$

### Proof {uses="thm:Poisson-summation-formula"}

Here we reproduce the proof given in [@ElkiesCohn].

The inequality

$$
\begin{equation*}
\sharp (X/\Lambda)\cdot f(0)\geq \sum_{x\in X}\sum_{y\in X/\Lambda}f(x-y)=\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\sum_{\ell\in  \Lambda}f(x-y+l)\end{equation*}
$$

follows from the condition (eqn:Cohn-Elkies-condition-1) of the theorem and the assumption on the distances between points in $X$.
The equality

$$
\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\sum_{\ell\in  \Lambda}f(x-y+l)=\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\,e^{2\pi i m(x-y)}.
$$

follows from the Poisson summation formula.
The right hand side of the above equation can be written as

$$
\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\,e^{2\pi i m(x-y)}=\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\cdot\big|\sum_{x\in X/\Lambda}e^{2\pi i m x}\big|^2.
$$

Note that $\big|\sum_{x\in X/\Lambda}e^{2\pi i m x}\big|^2\geq0$ for all $m\in\Lambda^*$. Moreover,  the term corresponding to $m=0$ satisfies $\big|\sum_{x\in X/\Lambda}e^{2\pi i 0 x}\big|^2=\sharp (X/\Lambda)^2$.
Now we use the condition (eqn:Cohn-Elkies-condition-2) and estimate

$$
\begin{equation*}\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\cdot\big|\sum_{x\in X/\Lambda}e^{2\pi i m(x-y)}\big|^2
\geq \frac{\sharp (X/\Lambda)^2}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\cdot \widehat{f}(0).
\end{equation*}
$$

Comparing inequalities (eqn: sharp X 1) and (eqn: sharp X 2) we arrive at

$$
\frac{\sharp (X/\Lambda)}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\leq \frac{f(0)}{\widehat{f}(0)}.
$$

Now we see that the density of the periodic packing $\mathcal{P}_X$ with balls of radius $1/2$ is bounded by

$$
\Delta(\mathcal{P}_X)=\frac{\sharp (X/\Lambda)}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\cdot{\mathrm{vol}(B_d(0,1/2))}\leq
\frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).
$$

This finishes the proof of the theorem for periodic packings.

## Theorem: Cohn--Elkies {\cite{ElkiesCohn}} {#thm:Cohn-Elkies-general lean="LinearProgrammingBound"}

Let $f:\mathbb{R}^d\to\mathbb{R}$ be a Schwartz function that is not identically zero and satisfies (eqn:Cohn-Elkies-condition-1) and (eqn:Cohn-Elkies-condition-2). Then the density of any $\Lambda$-periodic sphere packing is bounded above by 
$$
\frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).
$$

### Proof {uses="thm:Cohn-Elkies-periodic, thm:periodic-packing-optimal"}

The result follows immediately from [periodic-packing-optimal](#thm:periodic-packing-optimal) and [Cohn--Elkies {[@ElkiesCohn]}](#thm:Cohn-Elkies-periodic).

The main step in our proof of [MainTheorem](#MainTheorem) is the explicit construction of an optimal function. It will be convenient for us to scale this function by $\sqrt{2}$.

## Theorem: g {#thm:g uses="thm:g1"}

There exists a radial Schwartz function $g:\mathbb{R}^8\to\mathbb{R}$ which satisfies:

$$
\begin{align*}
g(x)&\leq 0\mbox{ for } \|x\|\geq \sqrt{2} \\
\widehat{g}(x)&\geq0\mbox{ for all } x\in\mathbb{R}^8\\
g(0)&=\widehat{g}(0)=1.
\end{align*}
$$

Theorem [Cohn--Elkies {[@ElkiesCohn]}](#thm:Cohn-Elkies-general) applied to the optimal function $f(x)=g(x/\sqrt{2})$ immediately implies [MainTheorem](#MainTheorem).

