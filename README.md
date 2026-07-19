# Sphere Packing in Lean — Lean Workspace

Interactive blueprint companion for
[Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean),
the Lean 4 formalization of Viazovska's solution to the sphere packing
problem in dimension 8. All 8 chapters of the upstream blueprint render here
as native chapters whose statuses, dependency edges, and source snippets are
recomputed from the compiled library — nothing is hand-maintained.

```bash
lake exe cache get             # prebuilt mathlib
lake build +SpherePacking      # compile the pinned upstream library
npm install && npm run dev     # site at http://localhost:8080
npm run blueprint:sync         # refresh kernel statuses after Lean changes
```

## Attribution

The mathematics here is the work of the
[Sphere Packing in Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)
project by Christopher Birkbeck, Sidharth Hariharan, Seewoo Lee, Gareth Ma,
Bhavik Mehta, and Maryna Viazovska — kickstarted at EPFL by Maryna Viazovska
and Sidharth Hariharan in March 2024, and maintained by Christopher Birkbeck,
Sidharth Hariharan, Bhavik Mehta, and Seewoo Lee.

- **Original blueprint site** —
  [thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint/)

The blueprint prose is converted from the upstream LaTeX sources, licensed
[Apache-2.0](UPSTREAM-LICENSE.txt); the Lean library itself is consumed as a
pinned Lake dependency. `vendor/upstream/` carries a copy of the pinned
revision's `.lean` sources so deployed site builds can render declaration
snippets without a Lake checkout — refresh it when bumping the pin. The
mathematical references cited by the blueprint live in `bibliography.bib`
(converted from the upstream bibliography) and render as linked citations.
