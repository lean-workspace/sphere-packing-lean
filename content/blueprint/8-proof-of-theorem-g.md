---
title: 'Proof of Theorem g'
type: "blueprint-chapter"
tags:
  - "blueprint"
---

Our proof of the [g](#thm:g) relies on the following two inequalities for modular objects.

## Proposition: ineqA {#prop:ineqA uses="lemma:ineqABnew-equiv, lemma:F-G-phi-psi-identities, lemma:F-G-pos, cor:ineqAnew"}

Consider the function $A:(0,\infty)\to\mathbb{C}$ defined as

$$
\begin{equation*}
A(t):=-t^2\phi_0(i/t)-\frac{36}{\pi^2}\,\psi_I(it).
\end{equation*}
$$

Then

$$
\begin{equation*}
    A(t) < 0
\end{equation*}
$$

for all $t > 0$.

## Proposition: ineqB {#prop:ineqB uses="lemma:ineqABnew-equiv, lemma:F-G-phi-psi-identities, cor:ineqBnew"}

Consider the function $B:(0,\infty)\to\mathbb{C}$ defined as

$$
\begin{equation*}
    B(t) := -t^2\phi_0(i/t)+\frac{36}{\pi^2}\,\psi_I(it)
\end{equation*}
$$

Then

$$
\begin{equation*}
    B(t) > 0
\end{equation*}
$$

for all $t > 0$.

Here we formalize the proof of the inequalities by Lee [Lee].
First, we can rewrite the inequality in [ineqA](#prop:ineqA) as follows.

## Definition: FG-definition {#def:FG-definition lean="F, G" uses="def:E2, def:Ek, def:H2-H3-H4"}

Define two (quasi) modular forms as

$$
\begin{align*}
    F(z) &= (E_2(z) E_4(z) - E_6(z))^2  \\
    G(z) &= H_2(z)^{3} (2 H_{2}(z)^{2} + 5 H_{2}(z) H_{4}(z) + 5 H_{4}(z)^{2}). 
\end{align*}
$$

## Lemma: F-G-phi-psi-identities {#lemma:F-G-phi-psi-identities uses="def:FG-definition, lemma:psi-new"}

We have

$$
\begin{align*}
    \phi_0 &= \frac{F}{\Delta}  \\
    \psi_S &= -\frac{1}{2} \frac{G}{\Delta}
\end{align*}
$$

### Proof

(eqn:phi0-F) is clear.
(eqn:psiS-G) is already shown in Lemma [psi-new](#lemma:psi-new).

## Lemma: ineqABnew-equiv {#lemma:ineqABnew-equiv uses="lemma:F-G-phi-psi-identities, def:psiI-psiT-psiS, cor:disc-pos"}

Inequality (eqn:ineqA) and (eqn:ineqB) are equivalent to

$$
\begin{align*}
    F(it) + \frac{18}{\pi^2} G(it) > 0  \\
    F(it) - \frac{18}{\pi^2} G(it) > 0 
\end{align*}
$$

respectively.

### Proof

By (eqn:psiS-define),

$$
\begin{equation*}
    \psi_I(it) = (\psi_S|_{-2}S)(it) = (it)^{2}\psi_S\left(-\frac{1}{it}\right) = -t^2 \psi_S\left(\frac{i}{t}\right).
\end{equation*}
$$

Combined with Lemma [F-G-phi-psi-identities](#lemma:F-G-phi-psi-identities) we can rewrite (eqn:ineqA) as

$$
\begin{equation*}
    A(t) = -t^2 \phi_0\left(\frac{i}{t}\right) + \frac{36}{\pi^2} \psi_S\left(\frac{i}{t}\right) < 0 \Leftrightarrow \frac{F(it)}{\Delta(it)} + \frac{18}{\pi^2} \frac{G(it)}{\Delta(it)} > 0
\end{equation*}
$$

for $t > 0$, which is equivalent to (eqn:ineqAnew) by Corollary [disc-pos](#cor:disc-pos).
Equivalences of (eqn:ineqB) and (eqn:ineqBnew) follows similarly; just change the sign.

Now, the first inequality (eqn:ineqAnew) follows from the positivity of each $F(it)$ and $G(it)$.

## Lemma: F-G-pos {#lemma:F-G-pos lean="F_imag_axis_pos, G_imag_axis_pos" uses="thm:ramanujan-formula, cor:theta-pos"}

For all $t > 0$, we have $F(it) > 0$ and $G(it) > 0$.

### Proof

By Ramanujan's identity (eqn:DE4), we have $F(z) = 9 E_4'(z)^2$ and

$$
\begin{equation*}
    F(it) = 9E_4'(it)^2 = 9 \left(240\sum_{n \geq 1} n \sigma_3(n) e^{-2 \pi n t} \right)^{2} > 0.
\end{equation*}
$$

$G(it) > 0$ follows from positivity of $H_2(it)$ and $H_4(it)$ (Lemma [theta-pos](#cor:theta-pos)).

## Corollary: ineqAnew {#cor:ineqAnew lean="FG_inequality_1" uses="lemma:F-G-pos"}

(eqn:ineqAnew) holds.

### Proof

This directly follows from Lemma [F-G-pos](#lemma:F-G-pos).

To prove the second inequality (eqn:ineqBnew), we need some identities satisfied by $F$ and $G$.

## Lemma: FG-de {#lemma:FG-de lean="MLDE_F, MLDE_G" uses="thm:ramanujan-formula, thm:serre-der-prod-rule, prop:theta-der, lemma:lv1-lv2-identities"}

$F$ and $G$ satisfy the following differential equations:

$$
\begin{align*}
    \partial_{12}\partial_{10} F - \frac{5}{6} E_{4} F &= 7200 \Delta (-E_{2}')  \\
    \partial_{12}\partial_{10} G - \frac{5}{6} E_{4} G &= -640 \Delta H_{2} 
\end{align*}
$$

### Proof

Both can be shown by direct computations.
By Ramanujan's identities (Theorem [ramanujan-formula](#thm:ramanujan-formula)) and the product rule of Serre derivatives (Theorem [serre-der-prod-rule](#thm:serre-der-prod-rule)), we have

$$
\begin{align*}
    \partial_{5} (E_2 E_4 - E_6) &= (E_2 E_4 - E_6)' - \frac{5}{12} E_2 (E_2 E_4 - E_6) \\
    &= \frac{E_2^2 - E_4}{12} \cdot E_4 + E_2 \cdot \frac{E_2 E_4 - E_6}{3} - \frac{E_2 E_6 - E_4^2}{2} - \frac{5}{12}E_2 (E_2 E_4 - E_6) \\
    &= -\frac{5}{12} (E_2 E_6 - E_4^2)  \\
    \partial_{7} (E_2 E_6 - E_4^2) &= (E_2 E_6 - E_4^2)' - \frac{7}{12} E_2 (E_2 E_6 - E_4^2) \\
    &= \frac{E_2^2 - E_4}{12} \cdot E_6 + E_2 \cdot \frac{E_2 E_6 - E_4^2}{2} - 2 E_4 \cdot \frac{E_2 E_4 - E_6}{3} - \frac{7}{12} E_2 (E_2 E_6 - E_4^2) \\
    &= -\frac{7}{12} E_4 (E_2 E_4 - E_6) 
\end{align*}
$$

and using these we can compute

$$
\begin{align*}
    \partial_{10} F &= \partial_{10} (E_2 E_4 - E_6)^2 \\
    &= 2 (E_2 E_4 - E_6) \partial_{5} (E_2 E_4 - E_6) \\
    &= -\frac{6}{5} (E_2 E_4 - E_6) (E_2 E_6 - E_4^2), \\
    \partial_{12}\partial_{10} F &= -\frac{5}{6} \partial_{12} ((E_2 E_4 - E_6) (E_2 E_6 - E_4)) \\
    &= -\frac{5}{6} (\partial_{5}(E_2 E_4 - E_6)) (E_2 E_6 - E_4^2) - \frac{5}{6} (E_2 E_4 - E_6) (\partial_{7} (E_2 E_6 - E_4)) \\
    &= \frac{25}{72} (E_2 E_6 - E_4^2)^2 + \frac{35}{72} E_4 (E_2 E_4 - E_6)^2, \\
    \partial_{12}\partial_{10}F - \frac{5}{6} E_4 F &= \frac{25}{72}(E_2 E_6 - E_4^2)^2 + \frac{35}{72} E_4 (E_2 E_4 - E_6)^2 - \frac{5}{6} E_4 (E_2 E_4 - E_6)^2 \\
    &= \frac{25}{72} ((E_2 E_6 - E_4^2)^2 - E_4 (E_2 E_4 - E_6)^2) \\
    &= \frac{25}{72} (- E_2^2 E_4^3 + E_2^2 E_6^2 + E_4^4 - E_4 E_6^3) \\
    &= -\frac{25}{72} (E_4^3 - E_6^2) (E_2^2 - E_4) \\
    &= 7200 \cdot \frac{E_4^3 - E_6^2}{1728} \cdot \frac{-E_2^2 + E_4}{12}\\
    &= 7200 \Delta (-E_2')
\end{align*}
$$

which proves (eqn:ddf).
Similarly, (eqn:ddg) can be proved using Proposition [theta-der](#prop:theta-der) and Lemma [lv1-lv2-identities](#lemma:lv1-lv2-identities).

## Corollary: MLDE-pos {#cor:MLDE-pos uses="lemma:FG-de, cor:disc-pos, cor:theta-pos, def:E2"}

(eqn:ddf) (resp. (eqn:ddg)) is positive (resp. negative) on the (positive) imaginary axis.

### Proof

From (eqn:E2) and Lemma [disc-pos](#cor:disc-pos),
\ifplastex

$$
\begin{equation*}
    7200 (-E_2'(it)) \Delta(it) = 7200 \cdot 24 \left(\sum_{n \ge 1} n \sigma_1(n) e^{-2 \pi n t}\right) \cdot \Delta(it) > 0.
\end{equation*}
$$

\else

$$
\begin{equation*}
    7200 (-E_2'(it)) \Delta(it) = 7200 \cdot 24 \left(\sum_{n \ge 1} n \sigma_1(n) e^{-2 \pi n t}\right) \cdot \Delta(it) > 0. \notag
\end{equation*}
$$

\fi
Negativity of (eqn:ddg), i.e. $-640 \Delta(it) H_2(it) < 0$ follows from Corollary [theta-pos](#cor:theta-pos) and [disc-pos](#cor:disc-pos).

The second inequality (eqn:ineqBnew) follows from the following two observations.
Since $G(it) > 0$ for all $t > 0$, we can define the quotient

$$
\begin{equation*}
    Q(t) := \frac{F(it)}{G(it)}
\end{equation*}
$$

as a function on $(0, \infty)$.

## Lemma: Qlim {#lemma:Qlim lean="FmodG_rightLimitAt_zero" uses="lemma:E2-transform-S, lemma:Ek-is-modular-form, lemma:theta-transform-S-T"}

We have

$$
\begin{equation*}
    \lim_{t \to 0^+} Q(t) = \frac{18}{\pi^2}.
\end{equation*}
$$

### Proof

We have

$$
\begin{equation*}
    \lim_{t \to 0^+} Q(t) = \lim_{t \to 0^+} \frac{F(it)}{G(it)} = \lim_{t \to \infty} \frac{F(i/t)}{G(i/t)}.
\end{equation*}
$$

By using the transformation laws of Eisenstein series (eqn:E2-S-transform), (eqn:Ek-trans-S) (for $k = 4, 6$) and the thetanull functions, (eqn:H2-transform-S), (eqn:H4-transform-S), we get

$$
\begin{align*}
    F\left(\frac{i}{t}\right) &= t^{12} F(it) - \frac{12t^{11}}{\pi} (E_2(it)E_4(it) - E_6(it))E_4(it) + \frac{36t^{10}}{\pi^2}E_4(it)^2, \\
    G\left(\frac{i}{t}\right) &= t^{10} H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5 H_{2}(it)^{2}).
\end{align*}
$$

Since $F$, $E_2 E_4 - E_6$ and $H_2$ are cusp forms, we have $\lim_{t \to \infty}t^k A(it) = 0$ when $A(z)$ is one of these forms and $k \geq 0$.
From $\lim_{t \to \infty} E_4(it) = 1 = \lim_{t \to \infty}H_{4}(it)$, we get

$$
\begin{align*}
    \lim_{t \to \infty} \frac{F(i/t)}{G(i/t)}
    &= \lim_{t \to \infty} \frac{t^{12} F(it) - \frac{12t^{11}}{\pi} (E_2(it)E_4(it) - E_6(it))E_4(it) + \frac{36t^{10}}{\pi^2}E_4(it)^2}{t^{10} H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5 H_{2}(it)^{2})} \\
    &= \lim_{t \to \infty} \frac{t^{2} F(it) - \frac{12t}{\pi} (E_2(it)E_4(it) - E_6(it))E_4(it) + \frac{36}{\pi^2}E_4(it)^2}{H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5 H_{2}(it)^{2})} \\
    &= \frac{18}{\pi^2}.
\end{align*}
$$

## Lemma: log-der-inf {#lemma:log-der-inf uses="lemma:der-q-series"}

Let $F$ be a quasimodular form where the vanishing order of $F$ at infinity is $n_0 > 0$, i.e. $F(z) = \sum_{n \geq n_0} a_n q^{n}$ with $a_{n_0} \ne 0$. Then

$$
\begin{equation*}
    \lim_{t \to \infty} \frac{F'(it)}{F(it)} = n_0.
\end{equation*}
$$

### Proof

By Lemma [der-q-series](#lemma:der-q-series),
    
$$
\begin{equation*}
        \lim_{t \to \infty} \frac{F'(it)}{F(it)} = \lim_{t \to \infty} \frac{\sum_{n \ge n_0} n a_n e^{-2 \pi n t}}{\sum_{n \ge n_0} a_n e^{-2 \pi n t}} = \lim_{t \to \infty} \frac{n_0 a_{n_0} e^{-2 \pi n_0 t} + O(e^{-2 \pi (n_0 + 1) t})}{a_{n_0} e^{-2 \pi n_0 t} + O(e^{-2 \pi (n_0 + 1) t})} = n_0.
    \end{equation*}
$$

## Proposition: Qdec {#prop:Qdec lean="FmodG_strictAntiOn" uses="thm:ramanujan-formula, thm:serre-der-prod-rule, cor:MLDE-pos, thm:anti-serre-der-pos, lemma:log-der-inf"}

The function $t \mapsto Q(t)$ is strictly decreasing.

### Proof

It is enough to show that

$$
\begin{align*}
    \frac{\mathrm{d}}{\mathrm{d} t} \left(\frac{F(it)}{G(it)}\right) < 0 &\Leftrightarrow (- 2\pi) \frac{F'(it)G(it) - F(it) G'(it)}{G(it)^{2}} < 0 \\
    &\Leftrightarrow F'(it) G(it) - F(it) G'(it) > 0 \\
    &\Leftrightarrow (\partial_{10}F)(it) G(it) - F(it) (\partial_{10}G)(it) > 0.
\end{align*}
$$

Let $\mathcal{L}_{1, 0} := (\partial_{10}F) G - F (\partial_{10} G) = F'G - FG'$.
Then

$$
\begin{align*}
\frac{\mathcal{L}_{1, 0}}{FG} = \frac{F'G - FG'}{FG} = \frac{F'}{F} - \frac{G'}{G}
\end{align*}
$$

The vanishing order of $F$ and $G$ at the infinity are $2$ and $\frac{3}{2}$ respectively, so by Lemma [log-der-inf](#lemma:log-der-inf), we have

$$
\begin{align*}
    \lim_{t \to \infty} \frac{\mathcal{L}_{1, 0}(it)}{F(it) G(it)} = \lim_{t \to \infty} \left(\frac{F'(it)}{F(it)} - \frac{G'(it)}{G(it)}\right) = 2 - \frac{3}{2} = \frac{1}{2} > 0
\end{align*}
$$

so $\mathcal{L}_{1, 0}(it) > 0$ for sufficiently large $t$.
Its Serre derivative $\partial_{22} \mathcal{L}_{1, 0}$ is positive by Corollary [MLDE-pos](#cor:MLDE-pos):

$$
\begin{align*}
    \partial_{22} \mathcal{L}_{1, 0} = (\partial_{12} \partial_{10} F) G - F (\partial_{12}\partial_{10} G)
    = \Delta (7200 (-E_{2}') G + 640 H_2 F) > 0.
\end{align*}
$$

Hence $\mathcal{L}_{1, 0}(it) > 0$ by Theorem [anti-serre-der-pos](#thm:anti-serre-der-pos), and the monotonicity follows.

## Corollary: ineqBnew {#cor:ineqBnew lean="FG_inequality_2" uses="lemma:Qlim, prop:Qdec, lemma:F-G-pos"}

(eqn:ineqBnew) holds.

### Proof

$$
\begin{equation*}
    \frac{F(it)}{G(it)} = Q(t) < \lim_{u \to 0^+} Q(u) = \frac{18}{\pi^2}
\end{equation*}
$$

and by Lemma [F-G-pos](#lemma:F-G-pos), (eqn:ineqBnew) follows.

Finally, we are ready to prove [g](#thm:g).

## Theorem: g1 {#thm:g1 uses="prop:a-fourier, prop:b-fourier, prop:a-double-zeros, prop:b-double-zeros, prop:ineqA, prop:ineqB, prop:a0, prop:b0"}

The function
$$g(x):=\frac{\pi\,i}{8640}a(x)+\frac{i}{240\pi}\,b(x)$$
satisfies conditions (eqn:g1)--(eqn:g3).

### Proof

First, we prove that (eqn:g1) holds. By Propositions [a-double-zeros](#prop:a-double-zeros) and [b-double-zeros](#prop:b-double-zeros) we know that for $r>\sqrt{2}$

$$
\begin{equation*} g(r)=\frac{\pi}{2160}\,\sin(\pi r^2/2)^2\,\int\limits_0^\infty A(t)\,e^{-\pi r^2 t}\,dt\end{equation*}
$$

where $$A(t)=-t^2\phi_0(i/t)-\frac{36}{\pi^2}\,\psi_I(it).$$
from the [ineqA](#prop:ineqA) we know that $A(t)<0\quad\mbox{for}\;t\in(0,\infty).$
Therefore identity (eqn:g A) implies (eqn:g1).

Next, we prove (eqn:g2). By Propositions [a-another-integral](#prop:a-another-integral) and [b-another-integral](#prop:b-another-integral) we know that for $r>0$

$$
\begin{equation*} \widehat{g}(r)=\frac{\pi}{2160}\,\sin(\pi r^2/2)^2\,\int\limits_0^\infty B(t)\,e^{-\pi r^2 t}\,dt\end{equation*}
$$

where $$B(t)=-t^2\phi_0(i/t)+\frac{36}{\pi^2}\,\psi_I(it).$$

Finally, the property (eqn:g3) readily follows from [a0](#prop:a0) and [b0](#prop:b0).
This finishes the proof of Theorems [g1](#thm:g1) and [g](#thm:g).

\begin{thebibliography}{20}

\bibitem{Bruinier} {\sc J. Bruinier}, _Borcherds products on O(2,l) and Chern classes of Heegner divisors_, Springer Lecture Notes in Mathematics 1780 (2002)

\bibitem{ElkiesCohn}  {\sc H. Cohn, N. Elkies}, _New upper bounds on sphere packings I_, Annals of Math. 157 (2003) pp. 689--714.

\bibitem{first course} {\sc F. Diamond, J. Shurman}, _A First Course in Modular Forms_, Springer New York, 2005.

\bibitem{Hejhal} {\sc D. Hejhal}, {\em The Selberg trace formula for $\mathrm{PSL}(2, \mathbb{R})$},  Springer Lecture Notes in Mathematics 1001 (1983)

\bibitem{Kohnen} {\sc W. Kohnen}, {\em A Very Simple Proof of the $q$-Product Expansion of the $\Delta$-Function}, The Ramanujan Journal 10 (2005): 71-73.

\bibitem{Lee} {\sc S. Lee}, {\em Algebraic proof of modular form inequalities for optimal sphere packings}, arXiv preprint arXiv:2406.14659 (2024).

\bibitem{Mumford} {\sc D. Mumford}, {\em Tata Lectures on Theta I}, Birkh\"auser, 1983.

\bibitem{Petersson32} {\sc H. Petersson}, {\em Ueber die Entwicklungskoeffizienten der automorphen Formen}, Acta Mathematica, Bd. 58 (1932),  pp. 169--215.

\bibitem{Rademacher38} {\sc H. Rademacher and H. S. Zuckerman}, {\em On the Fourier coefficients of certain modular forms of
positive dimension}, Annals of Math. (2) 39 (1938),  pp. 433--462.

\bibitem{Serre73} {\sc J. Serre}, {\em A Course in Arithmetic}, Springer New York, 1973.

\bibitem{Via2017} {\sc Maryna S. Viazovska}, {\em The sphere packing problem in dimension 8	},
Pages 991--1015 from Volume 185 (2017), Issue 3.

\bibitem{1-2-3} {\sc D. Zagier}, {\em Elliptic Modular Forms and Their Applications}, In:  The 1-2-3 of Modular Forms, (K. Ranestad, ed.) Norway, Springer Universitext, 2008.

\end{thebibliography}

{\footnotesize

Ecole Polytechnique Federale de Lausanne\\
1015 Lausanne\\
Switzerland\\
{\it Email address: maryna.viazovska@epfl.ch}}

