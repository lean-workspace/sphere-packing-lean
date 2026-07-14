import assert from "node:assert/strict"
import fs from "node:fs"
import os from "node:os"
import path from "node:path"
import { after, test } from "node:test"
import { buildBlueprintGraphView } from "./BlueprintGraph.tsx"

const fixtureRoot = fs.mkdtempSync(path.join(os.tmpdir(), "blueprint-graph-"))
const contentDir = path.join(fixtureRoot, "content")
const blueprintDir = path.join(contentDir, "blueprint")

fs.mkdirSync(blueprintDir, { recursive: true })
fs.writeFileSync(
  path.join(fixtureRoot, "blueprint.config.json"),
  JSON.stringify({ blueprints: [{ root: "blueprint" }] }),
)
fs.writeFileSync(
  path.join(blueprintDir, "dep-graph.canvas"),
  JSON.stringify({
    nodes: [
      {
        id: "def-sumodds",
        file: "blueprint/ch01_sumsofoddnumbers.md",
        subpath: "#def-sumodds",
        x: 0,
        y: 0,
      },
      {
        id: "lemma-sumodds-succ",
        file: "blueprint/ch01_sumsofoddnumbers.md",
        subpath: "#lemma-sumodds-succ",
        x: 200,
        y: 0,
      },
      {
        id: "thm-sumodds-eq-sq",
        file: "blueprint/ch01_sumsofoddnumbers.md",
        subpath: "#thm-sumodds-eq-sq",
        x: 400,
        y: 0,
      },
      {
        id: "lemma-sumodds-pos",
        file: "blueprint/ch01_sumsofoddnumbers.md",
        subpath: "#lemma-sumodds-pos",
        x: 600,
        y: 0,
      },
      {
        id: "thm-sum-first-cubes",
        file: "blueprint/ch02_sumsofcubes.md",
        subpath: "#thm-sum-first-cubes",
        x: 200,
        y: 120,
      },
      {
        id: "def-triangular",
        file: "blueprint/ch03_triangular.md",
        subpath: "#def-triangular",
        x: 400,
        y: 240,
      },
    ],
    edges: [
      {
        id: "statement-edge",
        fromNode: "def-sumodds",
        toNode: "thm-sum-first-cubes",
        dashed: true,
      },
      {
        id: "proof-edge",
        fromNode: "lemma-sumodds-succ",
        toNode: "thm-sum-first-cubes",
        dashed: false,
      },
      {
        id: "unrelated-edge",
        fromNode: "def-triangular",
        toNode: "thm-sum-first-cubes",
        dashed: false,
      },
    ],
  }),
)

after(() => fs.rmSync(fixtureRoot, { recursive: true, force: true }))

test("blueprint graph view scopes chapter items plus direct neighbors", () => {
  const graph = buildBlueprintGraphView(contentDir, "blueprint/ch01_sumsofoddnumbers")
  assert.ok(graph)

  const nodeIds = new Set(graph.nodes.map((node) => node.id))
  assert.deepEqual(graph.currentPageNodeIds, [
    "def-sumodds",
    "lemma-sumodds-succ",
    "thm-sumodds-eq-sq",
    "lemma-sumodds-pos",
  ])
  assert.equal(nodeIds.has("def-sumodds"), true)
  assert.equal(nodeIds.has("thm-sum-first-cubes"), true)
  assert.equal(nodeIds.has("def-triangular"), false)

  assert.ok(graph.edges.some((edge) => edge.from === "def-sumodds" && edge.kind === "statement"))
  assert.ok(graph.edges.some((edge) => edge.from === "lemma-sumodds-succ" && edge.kind === "proof"))
})

test("blueprint graph view leaves non-blueprint pages on the stock Quartz graph", () => {
  assert.equal(buildBlueprintGraphView(contentDir, "docs/quick-start"), null)
})
