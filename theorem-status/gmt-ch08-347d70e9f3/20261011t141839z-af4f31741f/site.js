"use strict";
// The data branch updates independently of slower GitHub Pages deployments.
let search, filter, rows;
let graphZoom = 1;
function bindGraph() {
  const svg = document.querySelector(".dag-svg");
  if (!svg) return;
  function zoom() {
    svg.style.width = `${graphZoom * 100}%`;
    svg.classList.toggle("zoomed", graphZoom > 1);
  }
  zoom();
  for (const button of document.querySelectorAll("[data-zoom]")) {
    button.addEventListener("click", () => {
      graphZoom = button.dataset.zoom === "reset" ? 1 : Math.max(1, Math.min(3,
        graphZoom + (button.dataset.zoom === "in" ? .25 : -.25)));
      zoom();
    });
  }
  const nodes = [...svg.querySelectorAll(".dag-node")];
  const edges = [...svg.querySelectorAll(".dag-edge")];
  function highlight(id) {
    const related = new Set([id]);
    for (const edge of edges) {
      if (edge.dataset.from === id || edge.dataset.to === id) {
        related.add(edge.dataset.from);
        related.add(edge.dataset.to);
      }
      edge.classList.toggle("related", edge.dataset.from === id || edge.dataset.to === id);
    }
    for (const node of nodes) node.classList.toggle("related", related.has(node.dataset.node));
    svg.classList.toggle("has-focus", Boolean(id));
  }
  for (const node of nodes) {
    node.addEventListener("mouseenter", () => highlight(node.dataset.node));
    node.addEventListener("mouseleave", () => highlight(null));
    node.addEventListener("focus", () => highlight(node.dataset.node));
    node.addEventListener("blur", () => highlight(null));
    node.addEventListener("click", event => {
      event.preventDefault();
      history.replaceState(null, "", node.getAttribute("href"));
      revealTarget();
    });
  }
}
function applyFilter() {
  const query = search.value.toLocaleLowerCase();
  let visible = 0;
  for (const row of rows) {
    const active = row.dataset.active === "true";
    const accepted = row.dataset.accepted === "true";
    const merged = row.dataset.merged === "true";
    const selected = filter.value === "all" || (active &&
      (filter.value === "active" || (filter.value === "accepted" ? accepted :
        filter.value === "merged" ? merged : !accepted)));
    row.hidden = !selected || !row.dataset.search.includes(query);
    if (!row.hidden) visible++;
  }
  document.getElementById("no-matches").hidden = visible > 0 || rows.length === 0;
}
function bindControls() {
  search = document.getElementById("search");
  filter = document.getElementById("filter");
  // Transitional wire alias keeps already-open v1 clients' acceptance filter
  // truthful. New clients expose the v2 names and root-only merge filter.
  const legacyAccepted = filter.querySelector('option[value="verified"]');
  if (legacyAccepted) legacyAccepted.value = "accepted";
  if (!filter.querySelector('option[value="merged"]')) {
    filter.add(new Option("Merged roots", "merged"));
  }
  rows = [...document.querySelectorAll("tbody tr[data-search]")];
  search.addEventListener("input", applyFilter);
  filter.addEventListener("change", applyFilter);
  bindGraph();
  applyFilter();
}
function revealTarget() {
  const row = document.getElementById(location.hash.slice(1));
  if (row && row.matches("tr[data-search]")) {
    filter.value = "all";
    search.value = "";
    applyFilter();
    row.querySelector("details").open = true;
    row.scrollIntoView({block: "center"});
  }
}
bindControls();
revealTarget();
window.addEventListener("hashchange", revealTarget);
let lastObservation = document.body.dataset.updated;
let liveConnected = false;
let fetchFailed = false;
function showFreshness() {
  const expiry = document.body.dataset.activityExpires;
  const expiredActivity = expiry && Date.now() >= Date.parse(expiry);
  const stale = expiredActivity || (document.body.dataset.lifecycle === "running" &&
    (!Number.isFinite(Date.parse(lastObservation)) || Date.now() - Date.parse(lastObservation) >
    (liveConnected ? 180 : Number(document.body.dataset.staleAfter || 1800)) * 1000));
  const notice = document.getElementById("stale");
  document.body.classList.toggle("observation-expired", stale);
  for (const assignment of document.querySelectorAll("[data-worker-assignment]")) {
    const expired = Date.now() >= Date.parse(assignment.dataset.expires);
    const prefix = expired ? "STALE: " : "Last seen: ";
    // Preserve the full SVG tooltip when updating the short node badge.
    const label = assignment.firstChild;
    if (label?.nodeType === Node.TEXT_NODE) label.textContent = prefix + assignment.dataset.label;
    assignment.classList.toggle("assignment-stale", expired);
  }
  notice.hidden = !stale && !fetchFailed;
  if (!notice.hidden) {
    notice.textContent = `${fetchFailed ? "Live feed unavailable. " : expiredActivity ? "Worker heartbeat is stale. " : "Status feed is stale. "}` +
      `Showing the last observation from ${lastObservation}. This is not confirmation that work is still running.`;
  }
}
function replaceSnapshot(payload) {
  const data = payload.snapshot;
  if (!data || data.schema_version !== 2 || data.repository !== repository || data.run !== run ||
      data.problem !== problem || !Number.isFinite(Date.parse(data.updated_at)) ||
      Date.parse(data.updated_at) > Date.now() + 30000) throw new Error("wrong status feed");
  if (Date.parse(data.updated_at) < Date.parse(lastObservation)) return;
  if (data.updated_at === lastObservation && liveConnected) return;
  const parsed = new DOMParser().parseFromString(payload.page, "text/html");
  if (parsed.body.dataset.statusSchema !== "2" || parsed.body.dataset.repository !== repository ||
      parsed.body.dataset.run !== run || parsed.body.dataset.problem !== problem ||
      parsed.body.dataset.updated !== data.updated_at) {
    throw new Error("incompatible status document");
  }
  // Live HTML may arrive in a tab that still has an older stylesheet.
  const stylesheet = parsed.querySelector('link[rel="stylesheet"]')?.getAttribute("href");
  const currentStyle = document.querySelector('link[rel="stylesheet"]');
  if (/^site-[a-f0-9]{12}\.css$/.test(stylesheet || "") && currentStyle?.getAttribute("href") !== stylesheet) {
    currentStyle.setAttribute("href", stylesheet);
  }
  const main = parsed.querySelector("main");
  if (!main || !main.querySelector("#search") || !main.querySelector("#stale")) {
    throw new Error("invalid status document");
  }
  // HTML comes from the same escaped renderer as Pages. Defense in depth:
  // remove executable elements and event handlers before inserting content.
  for (const unsafe of main.querySelectorAll("script,iframe,object,embed,style,link,meta,base")) unsafe.remove();
  for (const element of main.querySelectorAll("*")) {
    for (const attr of [...element.attributes]) {
      if (attr.name.toLowerCase().startsWith("on")) element.removeAttribute(attr.name);
    }
    for (const attr of ["href", "src", "action", "formaction"]) {
      if (element.hasAttribute(attr)) {
        const value = element.getAttribute(attr);
        if (!value.startsWith("#") && !value.startsWith("https://")) element.removeAttribute(attr);
      }
    }
  }
  const state = {query: search.value, filter: filter.value, x: scrollX, y: scrollY,
    focus: document.activeElement?.id, start: search.selectionStart, end: search.selectionEnd,
    expanded: rows.filter(row => row.querySelector("details")?.open).map(row => row.id),
    contract: document.querySelector(".contract")?.open,
    build: document.querySelector(".build-details")?.open,
    graphX: document.querySelector(".dag-viewport")?.scrollLeft || 0,
    graphY: document.querySelector(".dag-viewport")?.scrollTop || 0};
  document.querySelector("main").replaceWith(main);
  bindControls();
  search.value = state.query;
  filter.value = state.filter;
  for (const id of state.expanded) {
    const details = document.getElementById(id)?.querySelector("details");
    if (details) details.open = true;
  }
  const contract = document.querySelector(".contract");
  if (contract) contract.open = Boolean(state.contract);
  const build = document.querySelector(".build-details");
  if (build) build.open = Boolean(state.build);
  const graph = document.querySelector(".dag-viewport");
  if (graph) { graph.scrollLeft = state.graphX; graph.scrollTop = state.graphY; }
  applyFilter();
  if (["search", "filter"].includes(state.focus)) {
    document.getElementById(state.focus).focus({preventScroll: true});
    if (state.focus === "search") search.setSelectionRange(state.start, state.end);
  }
  scrollTo(state.x, state.y);
  document.body.dataset.lifecycle = data.lifecycle;
  document.body.dataset.updated = data.updated_at;
  document.body.dataset.staleAfter = data.stale_after_seconds || 180;
  document.body.dataset.activityExpires = data.activity_expires_at || "";
  lastObservation = data.updated_at;
  liveConnected = true;
  document.querySelector(".snapshot small").textContent =
    `Run ${data.lifecycle} · checks every 30s · publication delay may apply`;
}
// These fallbacks upgrade HTML emitted by an already-running older controller.
const repoLink = document.querySelector('header nav a[href^="https://github.com/"]');
const repository = document.body.dataset.repository || repoLink?.getAttribute("href").replace("https://github.com/", "");
const run = document.body.dataset.run || document.querySelector(".run code")?.textContent;
const problem = document.body.dataset.problem;
const match = location.pathname.match(/(theorem-status\/[a-z0-9-]+\/[a-z0-9-]+)(?:\/|\/index.html)?$/);
const liveURL = /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repository || "") && match ?
  `https://raw.githubusercontent.com/${repository}/status-live/${match[1]}/live.json` : null;
if (liveURL) {
  const feedLink = document.createElement("a");
  feedLink.href = liveURL;
  feedLink.textContent = "Live JSON";
  document.querySelector("header nav").append(feedLink);
}
let fetching = false;
async function poll() {
  if (fetching) return;
  fetching = true;
  try {
    if (!liveURL) throw new Error("no live endpoint");
    // GitHub's CDN ignores query-string cache busters for mutable raw files.
    // The publisher prepopulates minute paths, so changing the path every minute
    // yields a fresh cache key. The canonical file is a fallback, never evidence
    // of freshness on its own. Apply the newest successful observation only.
    const bucket = new Date().toISOString().slice(0, 16).replace(/[-:]/g, "");
    const urls = [liveURL.replace("/live.json", `/ticks/${bucket}.json`), liveURL];
    let success = false;
    await Promise.allSettled(urls.map(async url => {
      const response = await fetch(url, {cache: "no-store", credentials: "omit", signal: AbortSignal.timeout(15000)});
      if (!response.ok) throw new Error("live feed unavailable");
      replaceSnapshot(await response.json());
      success = true;
      fetchFailed = false;
      showFreshness();
    }));
    if (!success) throw new Error("live feed unavailable");
    fetchFailed = false;
  } catch (_) {
    fetchFailed = true;
    // Runs without a sidecar retain their ordinary Pages snapshot updates.
    if (!liveConnected) {
      try {
        const response = await fetch(`index.html?t=${Date.now()}`, {cache: "no-store", signal: AbortSignal.timeout(10000)});
        const text = await response.text();
        const parsed = new DOMParser().parseFromString(text, "text/html");
        if (response.ok && parsed.body.dataset.statusSchema === "2" &&
            parsed.body.dataset.repository === repository && parsed.body.dataset.run === run &&
            parsed.body.dataset.problem === problem &&
            Date.parse(parsed.body.dataset.updated) <= Date.now() + 30000 &&
            Date.parse(parsed.body.dataset.updated) > Date.parse(lastObservation) &&
            !search.value && !document.querySelector("details[open]")) location.reload();
      } catch (_) { /* Retain the last readable snapshot and show its age. */ }
    }
  } finally {
    fetching = false;
    showFreshness();
  }
}
showFreshness();
poll();
setInterval(poll, 30000);
setInterval(showFreshness, 10000);
document.addEventListener("visibilitychange", () => { if (!document.hidden) poll(); });
window.addEventListener("online", poll);
