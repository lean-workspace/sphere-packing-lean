---
title: "Sphere packings"
type: "blueprint-chapter"
tags:
  - "blueprint"
---

Scaffold chapter, migrated from chapter 1 of the
[upstream blueprint](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint/):
sphere packings as unions of separated open balls, and the density notions
leading to the sphere packing constant $\Delta_d$. Upstream labels are kept
verbatim (they coincide with the Lean declaration names).

## Definition: The SpherePacking structure {#SpherePacking lean="SpherePacking"}

A sphere packing is uniquely determined by its set of centres together with a
separation radius, so the formalization bundles exactly that identifying
information — and not the balls themselves — as the structure
`SpherePacking`: a set of centres $X \subset \mathbb{R}^d$ and a radius
$r > 0$ with $\|x - y\| \geq r$ for all distinct $x, y \in X$.

## Definition: Sphere packing {#SpherePacking.balls lean="SpherePacking.balls" uses="SpherePacking"}

Given a set $X \subset \mathbb{R}^d$ and a separation radius $r > 0$ such
that $\|x - y\| \geq r$ for all distinct $x, y \in X$, the *sphere packing*
$\mathcal{P}(X)$ with centres at $X$ is the union of all open balls of radius
$r$ centred at points in $X$:

$$\mathcal{P}(X) := \bigcup_{x \in X} B_d(x, r).$$

## Definition: Finite density {#SpherePacking.finiteDensity lean="SpherePacking.finiteDensity" uses="SpherePacking, SpherePacking.balls"}

The *finite density* of a packing $\mathcal{P}$ is defined as

$$\Delta_{\mathcal{P}}(R) := \frac{\mathrm{Vol}(\mathcal{P} \cap B_d(0,R))}{\mathrm{Vol}(B_d(0,R))}, \quad R > 0.$$

## Definition: Density {#SpherePacking.density lean="SpherePacking.density" uses="SpherePacking, SpherePacking.finiteDensity"}

The *density* of a packing $\mathcal{P}$ is the limit superior

$$\Delta_{\mathcal{P}} := \limsup_{R \to \infty} \Delta_{\mathcal{P}}(R).$$

## Definition: Sphere packing constant {#SpherePackingConstant lean="SpherePackingConstant" uses="SpherePacking.density"}

The *sphere packing constant* is the supremum of packing densities over all
possible packings:

$$\Delta_d := \sup_{\mathcal{P} \subset \mathbb{R}^d} \Delta_{\mathcal{P}}.$$
