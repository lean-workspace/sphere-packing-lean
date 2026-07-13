---
title: 'Fourier eigenfunctions with double zeroes at lattice points'
type: "blueprint-chapter"
tags:
  - "blueprint"
---

In this section we construct two radial Schwartz functions $a,b:\mathbb{R}^8\to i\mathbb{R}$ such that

$$
\begin{align*}\mathcal{F}(a)&=a\\
    \mathcal{F}(b)&=-b
\end{align*}
$$

which double zeroes at all $\Lambda_8$-vectors of length greater than $\sqrt{2}$. Recall that each vector of $\Lambda_8$ has length $\sqrt{2n}$ for some $n\in\mathbb{N}_{\geq 0}$.
We define $a$ and $b$ so that their values are purely imaginary because this simplifies some of our computations.
We will show in Section (sec: g) that an appropriate linear combination of functions $a$ and $b$ satisfies conditions (eqn:g1)--(eqn:g3).

Both of the functions will be defined via certain integrals of (quasi)modular forms.
Then the eigenfunction property mainly follows from the Poisson summation formula (Theorem [Poisson summation formula](#thm:Poisson-summation-formula)) and the transformation laws of (quasi)modular forms.
To apply Theorem [Poisson summation formula](#thm:Poisson-summation-formula), we will show that $a(x)$ and $b(x)$ are Schwartz functions, and this can be proved by verifying fast decay of the integrals.

First, we will define function $a$. To this end we consider the following functions:

## Definition: phi4-phi2-phi0 {#def:phi4-phi2-phi0 uses="def:Ek, def:E2"}

$$
\begin{align*}
    \phi_{-4} &:= \frac{E_4^2}{\Delta}  \\
    \phi_{-2} &:= \frac{E_4(E_2 E_4 - E_6)}{\Delta}  \\
    \phi_{0} &:= \frac{(E_2 E_4 - E_6)^2}{\Delta} 
\end{align*}
$$

The function $\phi_0(z)$ is not modular; however, it satisfies the following transformation rules:

## Lemma: phi0-transform {#lemma:phi0-transform uses="def:phi4-phi2-phi0, lemma:Ek-is-modular-form, lemma:E2-transform-S, lemma:disc-cuspform"}

We have

$$
\begin{align*}
    \phi_0(z + 1) &= \phi_0(z)  \\
    \phi_0\left(-\frac{1}{z}\right) &= \phi_0(z)-\frac{12i}{\pi}\,\frac{1}{z}\,\phi_{-2}(z)-\frac{36}{\pi^2}\,\frac{1}{z^2}\,\phi_{-4}(z).
\end{align*}
$$

### Proof

(eqn:phi0-trans-T) easily follows from periodicity of Eisenstein series and $\Delta(z)$.
For (eqn:phi0-trans-S),

$$
\begin{align*}
    \phi_{0}\left(-\frac{1}{z}\right) &= \frac{(E_2(-1/z) E_4(-1/z) - E_6(-1/z))^{2}}{\Delta(-1/z)} \\
    &= \frac{((z^2 E_2(z) - 6iz / \pi) \cdot z^4 E_4(z) - z^6 E_6(z))^{2}}{z^{12} \Delta(z)} \\
    &= \frac{\left(E_2(z) E_4(z) - E_6(z) - \frac{6i}{\pi z} E_4(z)\right)^2}{\Delta(z)} \\
    &= \frac{(E_2(z) E_4(z) - E_6(z))^{2} - \frac{12i}{\pi z}(E_2(z) E_4(z) - E_6(z)) E_4(z) - \frac{36}{\pi^2 z^2} E_4(z)^{2}}{\Delta(z)} \\
    &= \phi_0(z) - \frac{12 i}{\pi z} \phi_{-2}(z) - \frac{36}{\pi^2 z^2} \phi_{-4}(z).
\end{align*}
$$

For our formalization, we choose rectangular contours for the first and the second integral, and write it as follows.

## Definition: a-definition {#def:a-definition lean="MagicFunction.a.RealIntegrals.a', MagicFunction.a.RadialFunctions.a" uses="def:phi4-phi2-phi0"}

Define $a_{\mathrm{rad}} : \mathbb{R} \to \mathbb{C}$ by

$$
\begin{align*}
    a_\mathrm{rad}(r) := I_1(r) + I_2(r) + I_3(r) + I_4(r) + I_5(r) + I_6(r)
\end{align*}
$$

where

$$
\begin{align*}
    I_1(r) &:= \int_{-1}^{-1 + i} \phi_0 \left(\frac{-1}{z+1}\right) (z + 1)^2 e^{\pi i r z} \mathrm{d} z  \\
    I_2(r) &:= \int_{-1 + i}^{i} \phi_0 \left(\frac{-1}{z+1}\right) (z + 1)^2 e^{\pi i r z} \mathrm{d} z  \\
    I_3(r) &:= \int_{1}^{1 + i} \phi_0 \left(\frac{-1}{z-1}\right) (z - 1)^2 e^{\pi i r z} \mathrm{d} z  \\
    I_4(r) &:= \int_{1 + i}^{i} \phi_0 \left(\frac{-1}{z-1}\right) (z - 1)^2 e^{\pi i r z} \mathrm{d} z  \\
    I_5(r) &:= -2 \int_{0}^{i} \phi_0 \left(\frac{-1}{z}\right) z^2 e^{\pi i r z} \mathrm{d} z  \\
    I_6(r) &:= 2 \int_{i}^{i\infty} \phi_0(z) e^{\pi i r z} \mathrm{d} z 
\end{align*}
$$

Here all the contours are chosen to be straight line segments.
Now, define $a(x) := a_{\mathrm{rad}}(\|x\|^2)$ for $x \in \mathbb{R}^8$.

In the original paper, the integrals $I_1$ and $I_2$ are combined, as well as $I_3$ and $I_4$.
We choose to write them separately to simplify the formalization.

Now we prove that $a$ satisfies condition (eqn:a-fourier).
The following lemma will be used to prove Schwartzness of $a$ and $b$.

## Lemma: mod-div-disc-bound {#lemma:mod-div-disc-bound lean="MagicFunction.PolyFourierCoeffBound.DivDiscBoundOfPolyFourierCoeff"}

Let $f(z)$ be a holomorphic function with a Fourier expansion

$$
\begin{equation*}
    f(z) = \sum_{n \ge n_0} c_f(n) e^{\pi i n z}
\end{equation*}
$$

with $c_f(n_0) \ne 0$.
Assume that $c_f(n)$ has a polynomial growth, i.e. $|c_f(n)| = O(n^k)$ for some $k \in \mathbb{N}$.
Then there exists a constant $C_f > 0$ such that

$$
\begin{equation*}
    \left|\frac{f(z)}{\Delta(z)}\right| \le C_f e^{-\pi (n_0 - 2) \Im z}
\end{equation*}
$$

for all $z$ with $\Im z > 1/2$.

When $f(z)$ is a (quasi)modular form, we can take $k$ to be the weight of $f$.

> **Proof.** \uses{def:disc-definition}
By the product formula (eqn:disc-definition),

$$
\begin{align*}
    \left|\frac{f(z)}{\Delta(z)}\right| &= \left|\frac{\sum_{n \ge n_0} c_f(n) e^{\pi i n z}}{e^{2 \pi i z}\prod_{n \ge 1} (1 - e^{2\pi i n z})^{24}}\right| \\
    &= |e^{\pi i (n_0 - 2)z}| \cdot \frac{|\sum_{n \ge n_0} c_f(n) e^{\pi i (n - n_0) z}|}{\prod_{n \ge 1} |1 - e^{2\pi i n z}|^{24}} \\
    &\le e^{-\pi (n_0 - 2) \Im z} \cdot \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) \Im z}}{\prod_{n \ge 1} (1 - e^{- 2\pi n \Im z})^{24}} \\
    &\le e^{-\pi (n_0 - 2) \Im z} \cdot \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) / 2}}{\prod_{n \ge 1} (1 - e^{-\pi n})^{24}} \\
    &= C_f \cdot e^{-\pi (n_0 - 2) \Im z}
\end{align*}
$$

where

$$
\begin{equation*}
    C_f = \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) / 2}}{\prod_{n \ge 1} (1 - e^{-\pi n})^{24}}.
\end{equation*}
$$

Note that the summation in the numerator converges absolutely because of polynomial growth.
The denominator also converges, which is simply $e^{\pi} \cdot \Delta(i/2)$.

As corollaries, we have the following bound for $\phi_0$, $\phi_{-2}$, and $\phi_{-4}$.

## Corollary: phi0-bound {#cor:phi0-bound uses="thm:ramanujan-formula, lemma:mod-div-disc-bound, lemma:Ek-Fourier, lemma:mod_form_poly_growth"}

There exists a constant $C_0 > 0$ such that

$$
\begin{equation*}
|\phi_0(z)| \le C_0 e^{-2 \pi \Im z}
\end{equation*}
$$

for all $z$ with $\Im z > 1/2$.

### Proof

By Ramanujan's formula, $E_2 E_4 - E_6 = 3E_4' = 720 \sum_{n \ge 1} n \sigma_3(n) e^{2 \pi i n z}$ and
\ifplastex

$$
\begin{equation*}
    (E_2(z) E_4(z) - E_6(z))^{2} = 720^{2} e^{4 \pi i z} + O(e^{5 \pi i z}).
\end{equation*}
$$

\else

$$
\begin{equation*}
    (E_2(z) E_4(z) - E_6(z))^{2} = 720^{2} e^{4 \pi i z} + O(e^{5 \pi i z}). \notag
\end{equation*}
$$

\fi
Then the result follows from [mod-div-disc-bound](#lemma:mod-div-disc-bound) with $f(z) = (E_2 E_4 - E_6)^2$ and $n_0 = 4$.

## Corollary: phi2-bound {#cor:phi2-bound uses="def:phi4-phi2-phi0, lemma:mod-div-disc-bound, lemma:Ek-Fourier"}

There exists a constant $C_{-2} > 0$ such that

$$
\begin{equation*}
    |\phi_{-2}(z)| \le C_{-2}
\end{equation*}
$$

for all $z$ with $\Im z > 1/2$.

## Corollary: phi4-bound {#cor:phi4-bound uses="def:phi4-phi2-phi0, lemma:mod-div-disc-bound, lemma:Ek-Fourier"}

There exists a constant $C_{-4} > 0$ such that

$$
\begin{equation*}
    |\phi_{-4}(z)| \le C_{-4} e^{2 \pi \Im z}
\end{equation*}
$$

for all $z$ with $\Im z > 1/2$.

Note that we can take the constants $C_0$, $C_{-2}$, and $C_{-4}$ as

$$
\begin{align*}
    C_0 &= 9 \cdot 240^2 \cdot e^{\pi} \cdot \frac{E_4'(i/2)^{2}}{\Delta(i/2)} \notag \\
    C_{-2} &= 3 \cdot \frac{E_4(i/2) E_4'(i/2)}{\Delta(i/2)} \notag \\
    C_{-4} &= e^{-\pi} \cdot \frac{E_4(i/2)^{2}}{\Delta(i/2)}. \notag
\end{align*}
$$

## Lemma: integral-bound {#lem:integral-bound}

For all $n \in \mathbb{N}$, there exists a constant $C'$ such that for all $r \geq 0$,
    
$$
\begin{align*}
        r^n \cdot \int_{1}^{\infty} e^{-2\pi s} \, e^{-\pi r /s} \, \mathrm{d} s \leq C'
    \end{align*}
$$

### Proof

Fix $n \in \mathbb{N}$. We know there exists a constant $C$ such that for all $x \geq 0$, $\left\lvert x \right\rvert^n \cdot \left\lvert e^{-\pi x} \right\rvert \leq C$. In particular, for all $r \geq 0$ and $s \geq 1$, $r^n \cdot e^{-\pi r/s} \leq C s^n$. Hence, for all $r \in \mathbb{R}$, we can write
    
$$
\begin{align*}
        r^n \cdot \int_{1}^{\infty} e^{-2\pi s} \, e^{-\pi r /s} \, \mathrm{d}{s}
        = \int_{1}^{\infty} e^{-2\pi s} \, \left(\left\lvert r \right\rvert^n \cdot e^{-\pi r /s}\right) \, \mathrm{d}{s}
        \leq C \int_{1}^{\infty} e^{-2\pi s} \, s^n \, \mathrm{d}{s}
    \end{align*}
$$

    
    
    The $\Gamma$ function is given by
    
$$
\begin{align*}
        \Gamma(x) = \int_{0}^{\infty} e^{-u} \, u^{x-1} \, \mathrm{d}{u}
    \end{align*}
$$

    for all $x > 0$. Hence, writing $u = 2\pi s$ and using $\Gamma(n+1) = n!$, we get
    
    
$$
\begin{align*}
        C \int_{1}^{\infty} e^{-2\pi s} \, s^n \, \mathrm{d}{s}
        \leq C \int_{0}^{\infty} e^{-2\pi s} \, s^n \, \mathrm{d}{s}
        = C \int_{0}^{\infty} \frac{1}{(2\pi)^{n+1}} e^{-u} \, u^n \, \mathrm{d}{u}
        = \frac{C}{(2\pi)^n} \Gamma(n+1)
        = \frac{C \cdot n!}{(2\pi)^n}
    \end{align*}
$$

    Defining $C' := \frac{C \cdot n!}{(2\pi)^n}$ finishes the proof.

## Lemma: bound-I1-I3-I5 {#lem:bound-I1-I3-I5}

There exists $C > 0$ such that for all $r \geq 0$,
    
$$
\begin{equation*}
        |I_1(r)|, |I_3(r)|, |I_5(r)| \leq C \int_1^{\infty} e^{-2\pi s} \, e^{-\pi r / s} \, \mathrm{d} s.
    \end{equation*}
$$

### Proof

We only prove the bound for $I_1(r)$, as the other two are similar.
    By the change of variable $z = -1 + i t$ for $t \in [0,1]$, we have
    $$
    I_1(r) = -i \int_0^1 \phi_0\left(\frac{-1}{i t}\right) t^2 e^{-\pi i r} \cdot e^{-\pi r t} \, \mathrm{d} t.
    $$
    With the change of variable $s = 1 / t$, we get
    $$
    I_1(r) = i \int_1^{\infty} \phi_0(i s) \cdot s^{-4} \cdot e^{-\pi i r} \cdot e^{-\pi r / s} \, \mathrm{d} s
    $$
    and the absolute value can be bounded as
    $$
    |I_1(r)| \leq \int_1^{\infty} |\phi_0(i s)| \cdot s^{-4} \cdot |e^{-\pi i r}| \cdot e^{-\pi r / s} \, \mathrm{d} s \le \int_1^{\infty} |\phi_0(is)| \cdot e^{-\pi r / s} \, \mathrm{d} s.
    $$
    Now, [phi0-bound](#cor:phi0-bound) shows
    $$
    |I_1(r)| \leq C_0 \int_1^{\infty} e^{-2\pi s} \, e^{-\pi r / s} \, \mathrm{d} s.
    $$

Combined with [integral-bound](#lem:integral-bound), this shows that the integrals $I_1$, $I_3$, and $I_5$ decay faster than any polynomial as $r \to \infty$.
For the integrals $I_2$, $I_4$, and $I_6$, it is easier to see this since the contours are not touching the real axis.

## Lemma: bound-I2-I4-I6 {#lem:bound-I2-I4-I6}

There exist $C_1, C_2 > 0$ such that for all $r \geq 0$,
    
$$
\begin{equation*}
        |I_2(r)|, |I_4(r)| \leq C_1 e^{-\pi r}
    \end{equation*}
$$

    and
    
$$
\begin{equation*}
        |I_6(r)| \leq C_2 \frac{e^{-\pi(r + 2)}}{r + 2}
    \end{equation*}
$$

### Proof

For $I_2(r)$, parametrize $z$ as $z = t + i$ for $t \in [-1,0]$, and we have
    $$
        I_2(r) = \int_{-1}^0 \phi_0\left(\frac{-1}{t + 1 + i}\right) (t + 1 + i)^2 e^{\pi i r t} e^{-\pi r} \, \mathrm{d} t.
    $$
    Since the function $z \mapsto \phi_0\left(\frac{-1}{z+1}\right) (z+1)^2$ is holomorphic and bounded on the contour,
    there exists $C > 0$ such that $|\phi_0\left(\frac{-1}{z+1}\right) (z + 1)^2| \leq C$, and the absolute value of the integral can be bounded by
    $$
        |I_2(r)| \le \int_{-1}^{0} C e^{-\pi r} \, \mathrm{d} t = C e^{-\pi r}.
    $$
    The bound for $I_4(r)$ is similar.
    For $I_6(r)$, parametrize $z$ as $z = i t$ for $t \in [1, \infty)$, and we have
    $$
        I_6(r) = 2 i \int_1^{\infty} \phi_0(i t) e^{-\pi r t} \, \mathrm{d} t
    $$
    and the absolute value can be bounded as (using [phi0-bound](#cor:phi0-bound))
    $$
        |I_6(r)| \leq 2 \int_1^{\infty} |\phi_0(i t)| e^{-\pi r t} \, \mathrm{d} t \leq \frac{2C_0}{\pi} \int_1^{\infty} e^{-2\pi t} e^{-\pi r t} \, \mathrm{d} t = \frac{2C_0}{\pi} \frac{e^{-\pi (r + 2)}}{r + 2}.
    $$

Combining these, one can show that $a$ is a Schwartz function.

## Proposition: a-schwartz {#prop:a-schwartz lean="MagicFunction.FourierEigenfunctions.a" uses="def:a-definition, cor:phi0-bound"}

$a(x)$ is a Schwartz function.

### Proof {uses="lem:bound-I1-I3-I5, lem:bound-I2-I4-I6, lem:integral-bound, thm:smooth-fast-decay-schwartz"}

By Theorem [smooth-fast-decay-schwartz](#thm:smooth-fast-decay-schwartz), it suffices to show that the function is smooth and decays faster than any polynomial.
The smoothness follows from the ``differentiation under the integral'', which is already formalized in `mathlib`.
The decay follows from Lemmas [bound-I1-I3-I5](#lem:bound-I1-I3-I5) and [bound-I2-I4-I6](#lem:bound-I2-I4-I6), together with Lemma [integral-bound](#lem:integral-bound).

## Proposition: a-fourier {#prop:a-fourier lean="MagicFunction.a.Fourier.eig_a" uses="lemma:Ek-Fourier, def:E2, def:a-definition, lemma:Gaussian-Fourier, prop:a-schwartz"}

$a(x)$ satisfies (eqn:a-fourier).

### Proof

We recall that the Fourier transform of a Gaussian function is

$$
\begin{equation*}
    \mathcal{F}(e^{\pi i \|x\|^2 z})(y)=z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z}) }.
\end{equation*}
$$

Next, we exchange the contour integration with respect to $z$ variable and Fourier transform with respect to $x$ variable in (eqn:a-definition).
This can be done, since the corresponding double integral converges absolutely. In this way we obtain

$$
\begin{align*}
    \widehat{a}(y)=&\int\limits_{-1}^i\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz
    +\int\limits_{1}^i\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz\notag \\
    -&2\int\limits_{0}^i\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz +2\int\limits_{i}^{i\infty}\phi_0(z)\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz.\notag
\end{align*}
$$

Now we make a change of variables $w=\frac{-1}{z}$. We obtain

$$
\begin{align*}
    \widehat{a}(y)=&\int\limits_{1}^i\phi_0\Big(1-\frac{1}{w-1}\Big)\,(\frac{-1}{w}+1)^2\,w^{2}\,e^{\pi i \|y\|^2 \,w}\,dw\notag\\
    +&\int\limits_{-1}^i\phi_0\Big(1-\frac{1}{w+1}\Big)\,(\frac{-1}{w}-1)^2\,w^2\,e^{\pi i \|y\|^2 \,w}\,dw\\
    -&2\int\limits_{i \infty}^i\phi_0(w)\,e^{\pi i \|y\|^2 \,w}\,dw +2\int\limits_{i}^{0}\phi_0\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|y\|^2 \,w}\,dw.\notag
\end{align*}
$$

Since $\phi_0$ is $1$-periodic we have

$$
\begin{align*}
    \widehat{a}(y)\,=\,&\int\limits_{1}^i\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i \|y\|^2 \,z}\,dz
    +\int\limits_{-1}^i\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i \|y\|^2 \,z}\,dz\notag \\
    +&2\int\limits_{i}^{i\infty}\phi_0(z)\,e^{\pi i \|y\|^2 \,z}\,dz
    -2\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^{2}\,e^{\pi i \|y\|^2 \,z}\,dz\notag \\
    \,=\,&a(y).
\end{align*}
$$

This finishes the proof of the proposition.

Next, we check that $a$ has double zeroes at all $\Lambda_8$-lattice points of length greater then $\sqrt{2}$.
Using (eqn:phi0-bound), (eqn:phi2-bound), and (eqn:phi4-bound), we can control the behavior of $\phi_0$ near $0$ and $i\infty$.

## Corollary: phi0-near-0-infty {#cor:phi0-near-0-infty uses="cor:phi0-bound, cor:phi2-bound, cor:phi4-bound, lemma:phi0-transform"}

We have

$$
\begin{align*}
    \phi_0\left(\frac{i}{t}\right) &= O(e^{-2 \pi / t}) \quad \text{as } t \to 0  \\
    \phi_0\left(\frac{i}{t}\right) &= O(t^{-2}e^{2 \pi t}) \quad \text{as } t \to \infty.  \\
\end{align*}
$$

### Proof

The first estimate follows from (eqn:phi0-bound) with $z = i/t$.
For the second estimate, by (eqn:phi0-trans-S), (eqn:phi2-bound), and (eqn:phi4-bound), we have

$$
\begin{equation*}
    \left|\phi_0\left(\frac{i}{t}\right)\right| \le |\phi_0(it)| + \frac{12}{\pi t} |\phi_{-2}(it)| + \frac{36}{\pi^2 t^2} |\phi_{-4}(it)|
    \le C_0 e^{-2 \pi t} + \frac{12}{\pi t} \cdot C_{-2} + \frac{36}{\pi^2 t^2} \cdot C_{-4} e^{2 \pi t} = O(t^{-2}e^{2 \pi t}).
\end{equation*}
$$

## Proposition: a-double-zeros {#prop:a-double-zeros uses="cor:phi0-near-0-infty, def:a-definition, cor:disc-nonvanishing"}

For $r>\sqrt{2}$ we can express $a(r)$ in the following form

$$
\begin{equation*}
    a(r)=-4\sin(\pi r^2/2)^2\,\int\limits_{0}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz.
\end{equation*}
$$

### Proof

We denote the right hand side of (eqn: a double zeroes) by $d(r)$.
Convergence of the integral for $r > \sqrt{2}$ follows from [phi0-near-0-infty](#cor:phi0-near-0-infty).
We can write 

$$
\begin{align*}
    d(r)=&\int\limits_{-1}^{i\infty-1}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz-
    2\int\limits_{0}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz\notag\\
    +&\int\limits_{1}^{i\infty+1}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz.\notag
\end{align*}
$$

From (eqn:phi0-trans-S) we deduce that if $r>\sqrt{2}$ then
$\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\to 0$ as $\Im(z)\to\infty$. Therefore, we can deform the paths of integration
and rewrite

$$
\begin{align*}
    d(r)=&\int\limits_{-1}^{i}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz
    +\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz\notag\\
    -2&\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz
    -2\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz\notag\\
    +&\int\limits_{1}^{i}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz
    +\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz.\notag
\end{align*}
$$

Now from (eqn:phi0-trans-S) we find

$$
\begin{align*}&\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2-2\phi_0\Big(\frac{-1}{z}\Big)\,z^2+
\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2=\notag\\
&\phi_0(z+1)\,(z+1)^2-2\phi_0(z)\,z^2+\phi_0(z-1)\,(z-1)^2\notag\\
&-\frac{12i}{\pi}\,\Big(\phi_{-2}(z+1)\,(z+1)-2\phi_{-2}(z)\,z+\phi_{-2}(z-1)\,(z-1)\Big)\notag\\
&-\frac{36}{\pi^2}\Big(\phi_{-4}(z+1)-2\phi_{-4}(z)+\phi_{-4}(z-1)\Big)=\notag\\
&2\phi_0(z).
\end{align*}
$$

Thus, we obtain

$$
\begin{align*}
    d(r)=&\int\limits_{-1}^{i}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz
    -2\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz\notag\\
    +&\int\limits_{1}^{i}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz
    +2\int\limits_{i}^{i\infty}\phi_0(z)\,e^{\pi i r^2 \,z}\,dz=a(r).\notag
\end{align*}
$$

This finishes the proof.

Finally, we find another convenient integral representation for $a$ and compute values of $a(r)$ at $r=0$ and $r=\sqrt{2}$.

## Proposition: a-another-integral {#prop:a-another-integral uses="prop:a-double-zeros, def:phi4-phi2-phi0, lemma:phi0-transform, def:a-definition"}

For $r\geq0$ we have

$$
\begin{align*}a(r)=&4i\,\sin(\pi r^2/2)^2\,\Bigg(\frac{36}{\pi^3\,(r^2-2)}-\frac{8640}{\pi^3\,r^4}+\frac{18144}{\pi^3\,r^2}\\ +&\int\limits_0^\infty\,\left(t^2\,\phi_0\Big(\frac{i}{t}\Big)-\frac{36}{\pi^2}\,e^{2\pi t}+\frac{8640}{\pi}\,t-\frac{18144}{\pi^2}\right)\,e^{-\pi r^2 t}\,dt \Bigg) .\notag\end{align*}
$$

The integral converges absolutely for all $r\in\mathbb{R}_{\geq 0}$.

### Proof

Suppose that $r>\sqrt{2}$. Then by [a-double-zeros](#prop:a-double-zeros)
$$a(r)=4i\,\sin(\pi r^2/2)^2\,\int\limits_{0}^{\infty}\phi_0(i/t)\,t^2\,e^{-\pi r^2 t}\,dt. $$
From (eqn:phi0-trans-S) we obtain

$$
\begin{equation*}
\phi_0(i/t)\,t^2=\frac{36}{\pi^2}\,e^{2 \pi t}-\frac{8640}{\pi}\,t+\frac{18144}{\pi^2}+O(t^2\,e^{-2\pi t})\quad\mbox{as}\;t\to\infty.
\end{equation*}
$$

For $r>\sqrt{2}$ we have

$$
\begin{equation*}
\int\limits_0^\infty \left(\frac{36}{\pi^2}\,e^{2 \pi t}+\frac{8640}{\pi}\,t+\frac{18144}{\pi^2}\right)\,e^{-\pi r^2 t}\,dt
=\frac{36}{\pi^3\,(r^2-2)}-\frac{8640}{\pi^3\,r^4}+\frac{18144}{\pi^3\,r^2}.\end{equation*}
$$

Therefore, the identity (eqn:a-another-integral) holds for $r>\sqrt{2}$.

On the other hand, from the definition (eqn:a-definition) we see that $a(r)$ is analytic in some neighborhood of $[0,\infty)$. The asymptotic expansion (eqn: phi asymptotic) implies that the right hand side of (eqn:a-another-integral) is also analytic in some neighborhood of $[0,\infty)$. Hence, the identity (eqn:a-another-integral) holds on the whole interval $[0,\infty)$. This finishes the proof of the proposition.

From the identity (eqn:a-another-integral) we see that the values $a(r)$ are in $i\mathbb{R}$ for all $r\in\mathbb{R}_{\geq0}$.

## Proposition: a0 {#prop:a0 lean="MagicFunction.a.SpecialValues.a_zero" uses="prop:a-another-integral"}

We have $a(0) = -\frac{i}{8640}$.

### Proof

These identities follow immediately from the previous proposition.

Now we construct function $b$. To this end we consider the function

## Definition: h {#def: h uses="def:H2-H3-H4"}

$$
\begin{equation*}
    h(z) := 128 \frac{H_3(z) + H_4(z)}{H_2(z)^2}.
\end{equation*}
$$

It is easy to see that $h\in M^!_{-2}(\Gamma_0(2))$. Indeed, first we check that $h|_{-2}\gamma=h$
for all $\gamma\in\Gamma_0(2)$. Since the group $\Gamma_0(2)$ is generated by elements
$\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ and $\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)$
it suffices to check that $h$ is invariant under their action. This follows immediately
from (eqn:H2-transform-S)--(eqn:H4-transform-S) and (eqn: h define). Next we analyze the poles of $h$.
It is known [Mumford, Chapter I Lemma 4.1] that $\theta_{10}$ has no zeros in the upper-half plane and hence $h$ has poles only at the cusps.
At the cusp $i\infty$ this modular form has the Fourier expansion
\ifplastex

$$
\begin{equation*}
h(z)\,=\,q^{-1} + 16 - 132 q + 640 q^2 - 2550 q^3+O(q^4).
\end{equation*}
$$

\else

$$
\begin{equation*}
h(z)\,=\,q^{-1} + 16 - 132 q + 640 q^2 - 2550 q^3+O(q^4).\notag
\end{equation*}
$$

\fi
Let $I=\left(\begin{smallmatrix}1&0\\0&1\end{smallmatrix}\right)$,
$T=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)$, and
$S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ be elements of $\Gamma_1$.

## Definition: psiI-psiT-psiS {#def:psiI-psiT-psiS uses="def: h"}

We define the following three functions

$$
\begin{align*}
    \psi_I\,:=\,&h-h|_{-2}ST \\
    \psi_T\,:=\,&\psi_I|_{-2}T \\
    \psi_S\,:=\,&\psi_I|_{-2}S. 
\end{align*}
$$

## Lemma: psi-new {#lemma:psi-new}

$\psi_I(z), \psi_S(z), \psi_T(z)$ can be written as
    
$$
\begin{align*}
        \psi_I(z) &= \frac{H_4^3 (5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{2\Delta},  \\
        \psi_S(z) &= -\frac{H_2^3 (2 H_2^2 + 5 H_2 H_4 + 5 H_4^2)}{2 \Delta}.  \\
        \psi_T(z) &= \frac{H_3^3 (5 H_2^2 - 5 H_2 H_3 + 2 H_3^2)}{2 \Delta}
    \end{align*}
$$

### Proof

By Lemma [theta-transform-S-T](#lemma:theta-transform-S-T), we have

$$
\begin{align*}
    H_2|_{-2}ST = (-H_4)|_{-2}T = -H_3, \\
    H_3|_{-2}ST = (-H_3)|_{-2}T = -H_4, \\
    H_4|_{-2}ST = (-H_2)|_{-2}T = H_2.
\end{align*}
$$

Using these equations and Lemma [lv1-lv2-identities](#lemma:lv1-lv2-identities), we can rewrite $\psi_I(z)$ as

$$
\begin{align*}
    \psi_I(z) &= h(z) - h|_{-2}ST(z) \\
    &= 128 \frac{H_3 + H_4}{H_2^2} - 128 \frac{-H_4 + H_2}{H_3^2} \\
    &= 128 \frac{H_3^2 (H_3 + H_4) - H_2^2 (H_2 - H_4)}{H_2^2 H_3^2} \\
    &= 128 \frac{(H_2 + H_4)^2 (H_2 + 2 H_4) - H_2^2 (H_2 - H_4)}{H_2^2 H_3^2} \\
    &= 128 \frac{H_4(5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{ H_2^2 H_3^2} \\
    &= 128 \frac{H_4^3(5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{ H_2^2 H_3^2 H_4^3} \\
    &= \frac{H_4^3 (5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{2\Delta}.
\end{align*}
$$

Applying $|_{-2}S$ and $|_{-2}T$ to the expression of $\psi_I$ proves (eqn:psiS-new) and (eqn:psiT-new).

## Lemma: psiI-psiT-psiS-fourier {#lemma:psiI-psiT-psiS-fourier uses="lemma:psi-new"}

The Fourier expansions of these functions are

$$
\begin{align*}
    \psi_I(z)\,=\,&q^{-1} + 144 + O(q^{1/2}) \\
    \psi_T(z)\,=\,&q^{-1} + 144 + O(q^{1/2}) 
\end{align*}
$$

Now, we are ready to define function $b$.
Again, the definition here is slightly different from that in [Via2017], where all the contours are chosen to be the straight lines.

## Definition: b-definition {#def:b-definition uses="def:psiI-psiT-psiS"}

Define $b_\mathrm{rad} : \mathbb{R} \to \mathbb{C}$ by

$$
\begin{equation*}
    
    b_\mathrm{rad}(r) := J_1(r) + J_2(r) + J_3(r) + J_4(r) + J_5(r) + J_6(r)
\end{equation*}
$$

where for $r \in \mathbb{R}$,

$$
\begin{align*}
    J_1(r) &:= \int_{-1}^{-1 + i} \psi_T(z) e^{\pi i r z} \, \mathrm{d} z,  \\
    J_2(r) &:= \int_{-1 + i}^{i} \psi_T(z) e^{\pi i r z} \, \mathrm{d} z,  \\
    J_3(r) &:= \int_{1}^{1 + i} \psi_T(z) e^{\pi i r z} \, \mathrm{d} z,  \\
    J_4(r) &:= \int_{1 + i}^{i} \psi_T(z) e^{\pi i r z} \, \mathrm{d} z,  \\
    J_5(r) &:= -2 \int_{0}^{i} \psi_I(z) e^{\pi i r z} \, \mathrm{d} z,  \\
    J_6(r) &:= -2 \int_{i}^{i \infty} \psi_S(z) e^{\pi i r z} \, \mathrm{d} z. 
\end{align*}
$$

Here all the contours are straight line segments.
Then we define $b : \mathbb{R}^8 \to \mathbb{C}$ by $b(x) := b_\mathrm{rad}(\|x\|^2)$.

Now we prove that $b$ is a Schwartz function and satisfies condition (eqn:b-fourier).
As in the case of $a(x)$, we start with the following exponential bound of $\psi_S(z)$ and $\psi_I(z)$.

## Lemma: psi-bound {#lemma:psi-bound}

There exist constants $C_I, C_S, C_T > 0$ such that
    
$$
\begin{align*}
        |\psi_I(z)| &\le C_I e^{2\pi \Im z},  \\
        |\psi_T(z)| &\le C_T e^{2\pi \Im z},  \\
        |\psi_S(z)| &\le C_S e^{- \pi \Im z} 
    \end{align*}
$$

### Proof

The proof is similar to that of Lemma [phi0-bound](#cor:phi0-bound), follows from Lemma [mod-div-disc-bound](#lemma:mod-div-disc-bound) and the fact that the vanishing orders of the numerators of $\psi_I$, $\psi_T$, and $\psi_S$ at infinity are $0$, $0$ (i.e. not cusp forms), and $\frac{3}{2}$ respectively.

## Lemma: bound-J1-J3-J5 {#lemma:bound-J1-J3-J5}

There exist a constant $C > 0$ such that

$$
\begin{align*}
    |J_1(r)|, |J_3(r)|, |J_5(r)| &\le C \int_1^{\infty} e^{-\pi s} e^{\pi r / s}\, \mathrm{d} s.
\end{align*}
$$

## Lemma: bound-J2-J4-J6 {#lemma:bound-J2-J4-J6}

There exist $C_1, C_2 > 0$ such that
    
$$
\begin{align*}
        |J_2(r)|, |J_4(r)| &\le C_1 e^{-\pi r} \\
        |J_6(r)| &\le C_2 \frac{e^{\pi (r + 1)}}{r + 1}
    \end{align*}
$$

Combining Lemmas [bound-J1-J3-J5](#lemma:bound-J1-J3-J5), [bound-J2-J4-J6](#lemma:bound-J2-J4-J6), and Theorem [smooth-fast-decay-schwartz](#thm:smooth-fast-decay-schwartz), we can prove that $b(x)$ is a Schwartz function.

## Proposition: b-schwartz {#prop:b-schwartz lean="MagicFunction.FourierEigenfunctions.b" uses="lemma:psi-bound"}

$b(x)$ is a Schwartz function.

### Proof {uses="lemma:bound-J1-J3-J5, lemma:bound-J2-J4-J6, thm:smooth-fast-decay-schwartz"}

Similar to the proof of [a-schwartz](#prop:a-schwartz).

## Proposition: b-fourier {#prop:b-fourier lean="MagicFunction.b.Fourier.eig_b" uses="def:b-definition, lemma:Gaussian-Fourier, def:psiI-psiT-psiS, prop:b-schwartz"}

$b(x)$ satisfies (eqn:b-fourier).

### Proof

Here, we repeat the arguments used in the proof of [a-fourier](#prop:a-fourier).
We use identity (eqn:gaussian Fourier) and change contour integration in $z$ and Fourier transform in $x$. Thus we obtain

$$
\begin{align*}
    \mathcal{F}(b)(x)= & \int\limits_{-1}^{i}\psi_T(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz
        + \int\limits_{1}^{i}\psi_T(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz \notag \\
    -& 2\,\int\limits_{0}^{i}\psi_I(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz
    - 2\,\int\limits_{i}^{i\infty}\psi_S(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz. \notag
\end{align*}
$$

We make the change of variables $w=\frac{-1}{z}$ and arrive at

$$
\begin{align*}
    \mathcal{F}(b)(x)= & \int\limits_{1}^{i}\psi_T\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw
        + \int\limits_{-1}^{i}\psi_T\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw \notag \\
    -& 2\,\int\limits_{i\infty}^{i}\psi_I\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw
    - 2\,\int\limits_{i}^{0}\psi_S\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw.\notag
\end{align*}
$$

Now we observe that the definitions (eqn:psiI-define)--(eqn:psiS-define) imply

$$
\begin{align*}
    \psi_T|_{-2}S=&-\psi_T \notag \\
    \psi_I|_{-2}S=&\psi_S \notag \\
    \psi_S|_{-2}S=&\psi_I. \notag
\end{align*}
$$

Therefore, we arrive at

$$
\begin{align*}
    \mathcal{F}(b)(x)= & \int\limits_{1}^{i}-\psi_T(z)\,e^{\pi i \|x\|^2 z}\,dz
        + \int\limits_{-1}^{i}-\psi_T(z)\,e^{\pi i \|x\|^2 z}\,dz \notag \\
    +& 2\,\int\limits_{i}^{i\infty}\psi_S(z)\,e^{\pi i \|x\|^2 z}\,dz
    + 2\,\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i \|x\|^2 w}\,dw.\notag
\end{align*}
$$

Now from (eqn:b-definition) we see that
$$ \mathcal{F}(b)(x)=-b(x). $$

Now we regard the radial function $b$ as a function on $\mathbb{R}_{\geq0}$. We check that $b$ has double roots at $\Lambda_8$-points.

## Corollary: psiI-near-0-infty {#cor:psiI-near-0-infty uses="lemma:psi-bound, def:psiI-psiT-psiS"}

We have

$$
\begin{align*}
    \psi_I(it) &= O(t^2 e^{\pi/t}) \quad \text{as } t \to 0  \\
    \psi_I(it) &= O(e^{2 \pi t}) \quad \text{as } t \to \infty. 
\end{align*}
$$

### Proof

By (eqn:psiS-define), we have

$$
\begin{equation*}
    \psi_I(it) = (it)^{-2} \psi_S\left(\frac{-1}{it}\right) = -t^{-2} \psi_S\left(\frac{i}{t}\right).
\end{equation*}
$$

and combined with (eqn:psiS-bound) we get (eqn:psiI-near-0).
(eqn:psiI-near-infty) follows from Lemma [psi-bound](#lemma:psi-bound).

## Proposition: b-double-zeros {#prop:b-double-zeros uses="lemma:psiI-psiT-psiS-fourier, def:psiI-psiT-psiS, cor:psiI-near-0-infty, cor:disc-nonvanishing"}

For $r>\sqrt{2}$ function $b(r)$ can be expressed as

$$
\begin{equation*}
    b(r)=-4\sin(\pi r^2/2)^2\,\int\limits_{0}^{i\infty}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz.
\end{equation*}
$$

### Proof

We denote the right hand side of (eqn: b double zeroes) by $c(r)$.
By Corollary [psiI-near-0-infty](#cor:psiI-near-0-infty), the integral in (eqn: b double zeroes) converges for $r>\sqrt{2}$.
Then we rewrite it in the following way:
$$c(r)=\int\limits_{-1}^{i\infty-1}\psi_I(z+1)\,e^{\pi i r^2 \,z}\,dz-2\int\limits_{0}^{i\infty}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz+
\int\limits_{1}^{i\infty+1}\psi_I(z-1)\,e^{\pi i r^2 \,z}\,dz.$$
From the Fourier expansion (eqn: psi fourier I) we know that $\psi_I(z)=e^{-2\pi i z}+O(1)$ as $\Im(z)\to\infty$.
By assumption $r^2>2$, hence we can deform the path of integration and write

$$
\begin{align*}
\int\limits_{-1}^{i\infty-1}\psi_I(z+1)\,e^{\pi i r^2 \,z}\,dz=&
\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{i}^{i\infty}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz\\
\int\limits_{1}^{i\infty+1}\psi_I(z-1)\,e^{\pi i r^2 \,z}\,dz=&
\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{i}^{i\infty}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz.
\end{align*}
$$

We have

$$
\begin{align*}c(r)=&\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz
-2\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz\\
&+2\int\limits_{i}^{i\infty}(\psi_T(z)-\psi_I(z))\,e^{\pi i r^2 \,z}\,dz.\nonumber
    \end{align*}
$$

Next, we check that the functions $\psi_I,\psi_T$, and $\psi_S$ satisfy the following identity:

$$
\begin{equation*}\psi_T+\psi_S=\psi_I.\end{equation*}
$$

Indeed, from definitions (eqn:psiI-define)-(eqn:psiS-define) we get

$$
\begin{align*}\psi_T+\psi_S=&(h-h|_{-2}ST)|_{-2}T+(h-h|_{-2}ST)|_{-2}S\notag\\
=&h|_{-2}T-h|_{-2}ST^2+h|_{-2}S-h|_{-2}STS.\notag\end{align*}
$$

Note that $ST^2S$ belongs to $\Gamma_0(2)$. Thus, since $h\in M^!_{-2}\Gamma_0(2)$ we get
$$\psi_T+\psi_S=h|_{-2}T-h|_{-2}STS. $$
Now we observe that $T$ and $STS(ST)^{-1}$ are also in $\Gamma_0(2)$. Therefore,
$$\psi_T+\psi_S=h|_{-2}T-h|_{-2}STS=h|_{-2}-h|ST=\psi_I.$$

Combining (eqn: c1) and (eqn: c2) we find

$$
\begin{align*}c(r)=&\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz
-2\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz\notag\\
&-2\int\limits_{i}^{i\infty}\psi_S(z)\,e^{\pi i r^2 \,z}\,dz\notag\\
=&b(r).\notag
    \end{align*}
$$

At the end of this section we find another integral representation of $b(r)$ for $r\in\mathbb{R}_{\geq0}$ and compute special values of $b$.

## Proposition: b-another-integral {#prop:b-another-integral uses="prop:b-double-zeros, lemma:psiI-psiT-psiS-fourier, def:b-definition"}

For $r\geq0$ we have

$$
\begin{equation*}b(r)=4i\,\sin(\pi r^2/2)^2\,\left(\frac{144}{\pi\,r^2}+\frac{1}{\pi\,(r^2-2)}+\int\limits_0^\infty\,\left(\psi_I(it)-144-e^{2\pi t}\right)\,e^{-\pi r^2 t}\,dt\right).\end{equation*}
$$

The integral converges absolutely for all $r\in\mathbb{R}_{\geq 0}$.

### Proof

The proof is analogous to the proof of [a-another-integral](#prop:a-another-integral).
First, suppose that $r>\sqrt{2}$. Then by [b-double-zeros](#prop:b-double-zeros)
$$b(r)=4i\,\sin(\pi r^2/2)^2\,\int\limits_{0}^{\infty}\psi_I(it)\,e^{-\pi r^2 t}\,dt. $$
From (eqn: psi fourier I) we obtain

$$
\begin{equation*}
\psi_I(it)=e^{2\pi t}+144+O(e^{-\pi t})\quad\mbox{as}\;t\to\infty.
\end{equation*}
$$

For $r>\sqrt{2}$ we have

$$
\begin{equation*}
\int\limits_0^\infty \left(e^{2\pi t}+144\right)\,e^{-\pi r^2 t}\,dt
=\frac{1}{\pi\,(r^2-2)}+\frac{144}{\pi\,r^2}.\end{equation*}
$$

Therefore, the identity (eqn:b-another-integral) holds for $r>\sqrt{2}$.

On the other hand, from the definition (eqn:b-definition) we see that $b(r)$ is analytic in some neighborhood of $[0,\infty)$. The asymptotic expansion (eqn: psi asymptotic) implies that the right hand side of (eqn:b-another-integral) is also analytic in some neighborhood of $[0,\infty)$. Hence, the identity (eqn:b-another-integral) holds on the whole interval $[0,\infty)$. This finishes the proof of the proposition.

We see from (eqn:b-another-integral) that $b(r)\in i\mathbb{R}$ far all $r\in\mathbb{R}_\geq{0}$.
Another immediate corollary of this proposition is

## Proposition: b0 {#prop:b0 lean="MagicFunction.b.SpecialValues.b_zero" uses="prop:b-another-integral"}

We have $b(0) = 0$.

### Proof

These identities follow immediately from the previous proposition.

