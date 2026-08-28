import katex from "katex";
import "./styles.css";
import { edges, nodes, stages, theoremHref } from "./proof-data.js";

const appRoot = document.querySelector("#app");
const nodeById = new Map(nodes.map((node) => [node.id, node]));
const stageById = new Map(stages.map((stage) => [stage.id, stage]));
const dependencyParents = new Map(nodes.map((node) => [node.id, []]));

edges.forEach((edge) => dependencyParents.get(edge.to)?.push(edge.from));

function longestDependencyDepth(nodeId, visited = new Set()) {
  if (visited.has(nodeId)) return 0;
  const nextVisited = new Set(visited);
  nextVisited.add(nodeId);
  return Math.max(
    0,
    ...(dependencyParents.get(nodeId) ?? []).map((parentId) =>
      1 + longestDependencyDepth(parentId, nextVisited),
    ),
  );
}

const dependencyDepthLimit = Math.max(1, ...nodes.map((node) => longestDependencyDepth(node.id)));

function escapeHtml(value) {
  return String(value)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#039;");
}

function figureSrc(node) {
  return `./figures/${encodeURIComponent(node.visual)}.svg`;
}

function nodeMarkup(node) {
  const stage = stageById.get(node.stage);
  return `
    <button
      type="button"
      class="proof-node"
      data-node="${node.id}"
      data-visual="${node.visual}"
      aria-expanded="false"
      aria-controls="proof-detail"
      style="--node-color:${stage.color}"
    >
      <span class="node-visual" aria-hidden="true">
        <img src="${figureSrc(node)}" alt="" draggable="false">
      </span>
      <span class="node-copy">
        <span class="node-title">${escapeHtml(node.title)}</span>
        <span class="node-subtitle">${escapeHtml(node.subtitle)}</span>
        <span class="node-formula" data-math="${escapeHtml(node.formula)}"></span>
      </span>
      <span class="node-expand" aria-hidden="true">+</span>
    </button>`;
}

const stageMarkup = stages
  .map((stage) => {
    const stageNodes = nodes.filter((node) => node.stage === stage.id);
    return `
      <section class="proof-stage" data-stage="${stage.id}" style="--stage-color:${stage.color}">
        <header class="stage-heading">
          <span class="stage-number">${stage.number}</span>
          <h2>${escapeHtml(stage.title)}</h2>
        </header>
        <div class="stage-flow" data-count="${stageNodes.length}" style="--node-count:${stageNodes.length}">
          ${stageNodes.map(nodeMarkup).join("")}
        </div>
        <div class="stage-detail-slot"></div>
      </section>`;
  })
  .join("");

const dependencyLegend = Array.from({ length: dependencyDepthLimit }, (_, index) => {
  const depth = index + 1;
  return `
    <span class="dependency-legend-item" data-depth="${depth}" title="${depth} prerequisite layer${depth === 1 ? "" : "s"}">
      <span class="dependency-swatch" aria-hidden="true">${depth}</span>
    </span>`;
}).join("");

appRoot.innerHTML = `
  <main class="proof-app">
    <header class="proof-header">
      <div class="proof-kicker">Proof map</div>
      <h1>The architecture of the proof</h1>
      <p>From metric evolution to singularity models, controlled surgery, extinction, and the topological conclusion.</p>
    </header>

    <div class="map-summary">
      <span><strong>${nodes.length} steps</strong> across ${stages.length} stages</span>
      <div class="dependency-legend" aria-label="Prerequisite depth">
        <span class="dependency-legend-label">Prerequisite depth</span>
        <span class="dependency-legend-items">${dependencyLegend}</span>
      </div>
    </div>

    <div class="proof-map" aria-label="Dependency map for the proof">
      <svg class="edge-layer" aria-hidden="true">
        <defs>
          <marker
            id="arrowhead"
            viewBox="0 0 10 10"
            markerWidth="10"
            markerHeight="10"
            refX="9"
            refY="5"
            orient="auto"
            markerUnits="userSpaceOnUse"
          >
            <path d="M 0 1 L 9 5 L 0 9 Z"></path>
          </marker>
        </defs>
        <g class="edge-paths"></g>
      </svg>
      ${stageMarkup}
    </div>

    <article class="expanded-detail" id="proof-detail" hidden>
      <button type="button" class="detail-close" aria-label="Close explanation" title="Close explanation">
        <span aria-hidden="true">&times;</span>
      </button>
      <div class="detail-lead">
        <figure class="detail-figure">
          <img alt="" draggable="false">
          <div class="detail-canvas-host" hidden></div>
          <button type="button" class="detail-reset" aria-label="Reset 3D view" title="Reset 3D view" hidden>
            <span aria-hidden="true">&#8634;</span>
          </button>
        </figure>
        <div class="detail-intro">
          <div class="detail-stage"></div>
          <h2 class="detail-title"></h2>
          <div class="detail-subtitle"></div>
          <div class="detail-formula"></div>
          <p class="detail-summary"></p>
        </div>
      </div>
      <div class="detail-sections">
        <section class="detail-section">
          <h3>Precise statement</h3>
          <p class="detail-statement"></p>
        </section>
        <section class="detail-section detail-mechanism">
          <h3>Core mechanism</h3>
          <ol class="mechanism-list"></ol>
        </section>
        <section class="detail-section">
          <h3>Role in the proof</h3>
          <p class="detail-role"></p>
        </section>
      </div>
      <a class="theorem-link" target="_top">
        <span>
          <small>Open in the blueprint</small>
          <strong></strong>
        </span>
        <b aria-hidden="true">&#8594;</b>
      </a>
    </article>
  </main>`;

const proofMap = document.querySelector(".proof-map");
const edgeSvg = document.querySelector(".edge-layer");
const edgePaths = document.querySelector(".edge-paths");
const detail = document.querySelector(".expanded-detail");
const detailClose = detail.querySelector(".detail-close");
const detailFigure = detail.querySelector(".detail-figure");
const detailFigureImage = detailFigure.querySelector("img");
const detailCanvasHost = detailFigure.querySelector(".detail-canvas-host");
const detailReset = detailFigure.querySelector(".detail-reset");
const nodeElements = new Map(
  [...document.querySelectorAll(".proof-node")].map((element) => [element.dataset.node, element]),
);

document.querySelectorAll("[data-math]").forEach((element) => {
  katex.render(element.dataset.math, element, { throwOnError: false });
});

function svgElement(name, attributes) {
  const element = document.createElementNS("http://www.w3.org/2000/svg", name);
  Object.entries(attributes).forEach(([key, value]) => element.setAttribute(key, value));
  return element;
}

function stageIndex(nodeId) {
  return stages.findIndex((stage) => stage.id === nodeById.get(nodeId)?.stage);
}

function dependencyDepths(nodeId) {
  const depths = new Map();
  const queue = [{ id: nodeId, depth: 0 }];

  while (queue.length > 0) {
    const { id, depth } = queue.shift();
    if (depth >= dependencyDepthLimit) continue;

    dependencyParents.get(id)?.forEach((parentId) => {
      const parentDepth = depth + 1;
      const previousDepth = depths.get(parentId);
      if (previousDepth !== undefined && previousDepth <= parentDepth) return;
      depths.set(parentId, parentDepth);
      queue.push({ id: parentId, depth: parentDepth });
    });
  }

  return depths;
}

function clearDependencyState() {
  nodeElements.forEach((element) => {
    element.classList.remove("is-ancestor");
    element.removeAttribute("data-dependency-depth");
  });
}

function applyDependencyState() {
  clearDependencyState();
  if (!selectedId) return new Map();

  const depths = dependencyDepths(selectedId);
  depths.forEach((depth, nodeId) => {
    const element = nodeElements.get(nodeId);
    if (!element) return;
    element.classList.add("is-ancestor");
    element.dataset.dependencyDepth = String(depth);
  });
  return depths;
}

function usesSideChannel(edge) {
  const fromStageIndex = stageIndex(edge.from);
  const toStageIndex = stageIndex(edge.to);
  const selectedStageIndex = selectedId ? stageIndex(selectedId) : -1;
  const crossesExpandedDetail = selectedStageIndex >= fromStageIndex && selectedStageIndex < toStageIndex;
  return toStageIndex - fromStageIndex > 1 || crossesExpandedDetail;
}

function pathForEdge(edge, index, mapRect) {
  const from = nodeElements.get(edge.from)?.getBoundingClientRect();
  const to = nodeElements.get(edge.to)?.getBoundingClientRect();
  if (!from || !to) return "";

  const fromCenterX = from.left - mapRect.left + from.width / 2;
  const fromCenterY = from.top - mapRect.top + from.height / 2;
  const toCenterX = to.left - mapRect.left + to.width / 2;
  const toCenterY = to.top - mapRect.top + to.height / 2;

  const fromStageIndex = stageIndex(edge.from);
  const toStageIndex = stageIndex(edge.to);

  if (fromStageIndex === toStageIndex) {
    const leftToRight = fromCenterX <= toCenterX;
    const x1 = (leftToRight ? from.right : from.left) - mapRect.left;
    const x2 = (leftToRight ? to.left : to.right) - mapRect.left + (leftToRight ? -5 : 5);
    return `M ${x1} ${fromCenterY} L ${x2} ${toCenterY}`;
  }

  const channelX = proofMap.clientWidth - 6 - (index % 3) * 4;
  const x1 = fromCenterX;
  const y1 = from.bottom - mapRect.top;
  const x2 = toCenterX;
  const y2 = to.top - mapRect.top - 5;

  if (!usesSideChannel(edge)) {
    const middleY = y1 + (y2 - y1) / 2;
    return `M ${x1} ${y1} L ${x1} ${middleY} L ${x2} ${middleY} L ${x2} ${y2}`;
  }

  const leaveY = y1 + 13;
  const enterY = y2 - 13;

  return `M ${x1} ${y1} L ${x1} ${leaveY} L ${channelX} ${leaveY} L ${channelX} ${enterY} L ${x2} ${enterY} L ${x2} ${y2}`;
}

let selectedId = null;
let drawFrame = 0;
let interactiveFigure = null;
let interactiveFigureRequest = 0;
let interactiveFigureModule = null;

function drawEdges() {
  cancelAnimationFrame(drawFrame);
  drawFrame = requestAnimationFrame(() => {
    edgePaths.replaceChildren();
    const mapRect = proofMap.getBoundingClientRect();
    const width = proofMap.clientWidth;
    const height = proofMap.clientHeight;
    edgeSvg.setAttribute("viewBox", `0 0 ${width} ${height}`);

    const selectedDependencies = selectedId ? dependencyDepths(selectedId) : new Map();
    edges.forEach((edge, index) => {
      const path = svgElement("path", {
        d: pathForEdge(edge, index, mapRect),
        class: "edge-path",
        "data-from": edge.from,
        "data-to": edge.to,
        "marker-end": "url(#arrowhead)",
      });
      const sourceDepth = selectedDependencies.get(edge.from);
      const targetDepth = selectedDependencies.get(edge.to);
      const isDependencyEdge = Boolean(
        selectedId &&
          sourceDepth !== undefined &&
          (edge.to === selectedId || targetDepth !== undefined),
      );

      if (isDependencyEdge) {
        const depth = sourceDepth;
        path.classList.add("is-dependency", `is-dependency-depth-${depth}`);
        path.dataset.dependencyDepth = String(depth);
      } else if (selectedId && edge.from !== selectedId && edge.to !== selectedId) {
        path.classList.add("is-muted");
      }
      if (selectedId && (edge.from === selectedId || edge.to === selectedId)) {
        path.classList.add("is-active");
      }
      if (usesSideChannel(edge)) path.classList.add("is-side-route");
      edgePaths.append(path);
    });
  });
}

function renderDetail(node) {
  const stage = stageById.get(node.stage);
  detail.style.setProperty("--detail-color", stage.color);
  detail.querySelector(".detail-stage").textContent = `${stage.number}. ${stage.title}`;
  detail.querySelector(".detail-title").textContent = node.title;
  detail.querySelector(".detail-subtitle").textContent = node.subtitle;
  detail.querySelector(".detail-summary").textContent = node.summary;
  detail.querySelector(".detail-statement").textContent = node.statement;
  detail.querySelector(".detail-role").textContent = node.role;

  detailFigureImage.src = figureSrc(node);
  detailFigureImage.alt = `Geometric diagram for ${node.title}`;

  katex.render(node.formula, detail.querySelector(".detail-formula"), {
    displayMode: true,
    throwOnError: false,
  });

  detail.querySelector(".mechanism-list").replaceChildren(
    ...node.mechanism.map((step) => {
      const item = document.createElement("li");
      item.textContent = step;
      return item;
    }),
  );

  const theoremLink = detail.querySelector(".theorem-link");
  theoremLink.href = theoremHref(node.theorem);
  theoremLink.querySelector("strong").textContent = node.theorem.title;
}

function disposeInteractiveFigure() {
  interactiveFigureRequest += 1;
  interactiveFigure?.dispose();
  interactiveFigure = null;
  detailCanvasHost.replaceChildren();
  detailCanvasHost.hidden = true;
  detailReset.hidden = true;
  detailFigureImage.hidden = false;
}

async function mountDetailInteractiveFigure(node) {
  disposeInteractiveFigure();
  const request = interactiveFigureRequest;
  detailCanvasHost.hidden = false;

  try {
    interactiveFigureModule ??= import("./interactive-figure.js");
    const { mountInteractiveFigure } = await interactiveFigureModule;
    if (request !== interactiveFigureRequest || selectedId !== node.id) return;
    const mounted = mountInteractiveFigure(detailCanvasHost, node.visual);
    if (!mounted) {
      detailCanvasHost.hidden = true;
      return;
    }
    interactiveFigure = mounted;
    detailFigureImage.hidden = true;
    detailReset.hidden = false;
  } catch (error) {
    console.warn("Interactive figure unavailable; using the vector fallback.", error);
    detailCanvasHost.hidden = true;
  }
}

function selectNode(id) {
  const node = nodeById.get(id);
  const selectedElement = nodeElements.get(id);
  if (!node || !selectedElement) return;

  if (selectedId === id) {
    clearSelection({ restoreFocus: true });
    return;
  }

  selectedId = id;
  applyDependencyState();
  nodeElements.forEach((element, nodeId) => {
    const selected = nodeId === id;
    element.classList.toggle("is-selected", selected);
    element.setAttribute("aria-expanded", String(selected));
    element.querySelector(".node-expand").textContent = selected ? "-" : "+";
  });

  renderDetail(node);
  document.querySelector(`[data-stage="${node.stage}"] .stage-detail-slot`).append(detail);
  detail.hidden = false;
  mountDetailInteractiveFigure(node);
  drawEdges();
}

function clearSelection({ restoreFocus = false } = {}) {
  const previous = selectedId;
  selectedId = null;
  applyDependencyState();
  disposeInteractiveFigure();
  detail.hidden = true;
  nodeElements.forEach((element) => {
    element.classList.remove("is-selected");
    element.setAttribute("aria-expanded", "false");
    element.querySelector(".node-expand").textContent = "+";
  });
  drawEdges();
  if (restoreFocus && previous) nodeElements.get(previous)?.focus();
}

nodeElements.forEach((element, id) => {
  element.addEventListener("click", () => selectNode(id));
});

detailClose.addEventListener("click", () => clearSelection({ restoreFocus: true }));
detailReset.addEventListener("click", () => interactiveFigure?.reset());
window.addEventListener("keydown", (event) => {
  if (event.key === "Escape" && selectedId) clearSelection({ restoreFocus: true });
});

function resizeHostFrame() {
  if (!window.frameElement) return;
  const height = Math.ceil(document.body.scrollHeight);
  window.frameElement.style.height = `${height}px`;
}

const resizeObserver = new ResizeObserver(() => {
  drawEdges();
  resizeHostFrame();
});
resizeObserver.observe(proofMap);
resizeObserver.observe(document.body);

document.fonts?.ready.then(drawEdges);
window.addEventListener("load", () => {
  drawEdges();
  resizeHostFrame();
});
drawEdges();
resizeHostFrame();
