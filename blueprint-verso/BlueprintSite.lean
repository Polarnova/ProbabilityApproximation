/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import VersoManual

open Verso Doc
open Verso.Genre Manual

namespace BlueprintSite

/-- Reader-facing build profile for Blueprint HTML. -/
inductive Profile where
  | dev
  | release
deriving BEq

/-- A source tree whose declaration locations can be linked to an immutable GitHub revision. -/
structure SourceRepository where
  pathPrefix : String
  sourceRoot : String

/-- Construct a GitHub source-tree mapping at an exact revision. -/
def SourceRepository.github (pathPrefix repository revision : String) : SourceRepository where
  pathPrefix := pathPrefix
  sourceRoot := s!"https://github.com/{repository}/blob/{revision}/"

/-- Read `BLUEPRINT_PROFILE`, defaulting to the public release presentation. -/
def readProfile : IO Profile := do
  match (← IO.getEnv "BLUEPRINT_PROFILE").getD "release" with
  | "dev" => pure .dev
  | "release" => pure .release
  | value => throw <| IO.userError s!"invalid BLUEPRINT_PROFILE '{value}'; expected dev or release"

/-- Read a source revision supplied by the publication shell. -/
def sourceRevision (name fallback : String) : IO String := do
  return (← IO.getEnv name).getD fallback

/-- Shared reader layout, dark theme, and source-link presentation. -/
def readerCss : CSS := ⟨r##"
@media screen and (min-width: 701px) {
  html[data-bp-style="blueprint"] .header-title-wrapper {
    box-sizing: border-box;
    min-width: 0;
    padding-right: calc(var(--search-bar-width) + 1rem);
  }

  html[data-bp-style="blueprint"] .header-title {
    font-size: clamp(1rem, 1.4vw, 1.5rem);
    overflow: hidden;
    text-overflow: ellipsis;
  }
}

html[data-bp-style="blueprint"]
  .bp_wrapper[id$="--statement"]:has(+ .bp_code_panel_wrapper) {
  margin-bottom: 0;
  border-bottom: 0;
  border-bottom-left-radius: 0;
  border-bottom-right-radius: 0;
}

html[data-bp-style="blueprint"]
  .bp_wrapper[id$="--statement"] + .bp_code_panel_wrapper {
  margin-top: 0;
  border-top-left-radius: 0;
  border-top-right-radius: 0;
}

.bp_external_decl_header_status.bp_external_decl_ok,
.bp_code_decl_status.bp_code_decl_status_ok {
  display: none;
}

html:not([data-bp-tags-ready]) .bp_metadata_tags {
  visibility: hidden;
}

.bp_external_decl_source {
  gap: 0;
}

.bp_external_decl_source::before {
  content: none;
}

a.bp_external_decl_source_link {
  display: inline-flex;
  min-width: 0;
  max-width: min(46rem, 78vw);
  align-items: baseline;
  gap: 0.28rem;
  color: #0969da !important;
  font-size: 0.71rem;
  font-weight: 700;
  text-decoration-line: underline;
  text-decoration-thickness: 0.08em;
  text-underline-offset: 0.14rem;
}

a.bp_external_decl_source_link:hover {
  color: #0550ae !important;
  text-decoration-thickness: 0.13em;
}

.bp_external_decl_source_action {
  flex: 0 0 auto;
}

.bp_external_decl_source_location {
  min-width: 0;
  overflow: hidden;
  color: inherit;
  font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace;
  font-size: 0.66rem;
  font-weight: 600;
  overflow-wrap: anywhere;
  text-overflow: ellipsis;
}

#bp-style-switcher select {
  color: var(--bp-color-text-strong);
}

html[data-bp-color-theme="dark"] {
  color-scheme: dark;
  --verso-background-color: #0b1120;
  --verso-surface-color: #111827;
  --verso-text-color: #e5e7eb;
  --verso-code-color: #e2e8f0;
  --verso-structure-color: #f8fafc;
  --verso-selected-color: #1e3a5f;
  --verso-info-color: #dbeafe;
  --verso-warning-color: #fde68a;
  --verso-error-color: #fca5a5;
  --verso-code-const-color: #93c5fd;
  --verso-code-keyword-color: #c4b5fd;
  --verso-code-var-color: #5eead4;
  --verso-toc-background-color: #0f172a;
  --verso-toc-text-color: #e2e8f0;
  --verso-toc-border-color: #334155;
  --verso-toc-resize-handle-color: #64748b;
  --verso-burger-toc-visible-shadow-color: #0b1120;
  --verso-burger-toc-hidden-color: #e2e8f0;
  --verso-burger-toc-hidden-shadow-color: #0b1120;
  --bp-color-surface: #111827;
  --bp-color-surface-muted: #172033;
  --bp-color-surface-subtle: #182235;
  --bp-color-surface-modern: #111d31;
  --bp-color-surface-warn: #3a2712;
  --bp-color-surface-warn-soft: #4a2f12;
  --bp-color-surface-note: #352b13;
  --bp-color-border: #475569;
  --bp-color-border-soft: #334155;
  --bp-color-border-muted: #475569;
  --bp-color-border-panel: #3f4d61;
  --bp-color-border-strong: #64748b;
  --bp-color-text-strong: #f8fafc;
  --bp-color-text: #e5e7eb;
  --bp-color-text-muted: #cbd5e1;
  --bp-color-text-subtle: #aebdd0;
  --bp-color-text-faint: #94a3b8;
  --bp-color-link: #7dd3fc;
  --bp-color-accent: #2dd4bf;
  --bp-color-accent-success: #4ade80;
  --bp-color-accent-warning: #facc15;
  --bp-color-accent-danger: #f87171;
  --bp-color-accent-info: #c4b5fd;
  --bp-color-status-success-text: #86efac;
  --bp-color-status-warning-text: #fde68a;
  --bp-color-status-warning-strong: #fdba74;
  --bp-color-status-warning-border: #b45309;
  --bp-color-status-warning-border-soft: #92400e;
  --bp-color-status-error-text: #fca5a5;
  --bp-color-status-error-strong: #fecaca;
  --bp-color-status-error-border-soft: #991b1b;
  --bp-color-status-note-border: #a16207;
  --bp-color-status-note-text: #fde68a;
  --bp-color-focus-border: #60a5fa;
  --bp-color-focus-surface: #172554;
  --bp-color-focus-ring: rgba(96, 165, 250, 0.25);
  --bp-color-selection: rgba(96, 165, 250, 0.25);
  --bp-color-selection-ring: rgba(96, 165, 250, 0.36);
  --bp-color-selection-surface-strong: rgba(96, 165, 250, 0.34);
  --bp-color-selection-surface-soft: rgba(96, 165, 250, 0.2);
  --bp-color-selection-surface-faint: rgba(96, 165, 250, 0.14);
  --bp-color-selection-shadow-strong: rgba(96, 165, 250, 0.42);
  --bp-color-selection-shadow-soft: rgba(96, 165, 250, 0.32);
  --bp-color-selection-shadow-faint: rgba(96, 165, 250, 0.22);
  --bp-color-target-ring: rgba(96, 165, 250, 0.34);
  --bp-color-target-surface: rgba(96, 165, 250, 0.18);
  --bp-color-target-ring-strong: rgba(96, 165, 250, 0.44);
  --bp-color-modern-border: #40516a;
  --bp-color-modern-surface-alt: #14213a;
  --bp-color-modern-caption: #1e3a5f;
  --bp-color-bold-surface-glow-1: rgba(245, 158, 11, 0.14);
  --bp-color-bold-surface-glow-2: rgba(20, 184, 166, 0.14);
  --bp-color-bold-link: #fdba74;
  --bp-color-bold-label: #d97706;
  --bp-color-biblio-border: #6d5b99;
  --bp-color-biblio-surface: #211b35;
  --bp-color-biblio-border-soft: #51436f;
  --bp-color-biblio-surface-soft: #1b1729;
  --bp-color-biblio-link: #c4b5fd;
  --bp-shadow-sm: 0 4px 14px rgba(0, 0, 0, 0.32);
  --bp-shadow-md: 0 10px 24px rgba(0, 0, 0, 0.42);
  --bp-shadow-lg: 0 12px 28px rgba(0, 0, 0, 0.48);
  --bp-shadow-modern: 0 6px 18px rgba(0, 0, 0, 0.3);
}

html[data-bp-color-theme="dark"],
html[data-bp-color-theme="dark"] body,
html[data-bp-color-theme="dark"] header {
  background: var(--verso-background-color);
  color: var(--verso-text-color);
}

html[data-bp-color-theme="dark"] header {
  box-shadow: 0 0 6px #020617;
}

html[data-bp-color-theme="dark"] .header-title,
html[data-bp-color-theme="dark"] h1,
html[data-bp-color-theme="dark"] h2,
html[data-bp-color-theme="dark"] h3,
html[data-bp-color-theme="dark"] h4,
html[data-bp-color-theme="dark"] h5,
html[data-bp-color-theme="dark"] h6 {
  color: var(--verso-structure-color);
}

html[data-bp-color-theme="dark"] a {
  color: var(--bp-color-link);
}

html[data-bp-color-theme="dark"] a.bp_external_decl_source_link {
  color: #7dd3fc !important;
}

html[data-bp-color-theme="dark"] a.bp_external_decl_source_link:hover {
  color: #bae6fd !important;
}

html[data-bp-color-theme="dark"] .bp_external_decl_meta,
html[data-bp-color-theme="dark"] .bp_external_decl_header_meta {
  color: var(--bp-color-text-subtle);
}

html[data-bp-color-theme="dark"] .bp_graph_legend_popover,
html[data-bp-color-theme="dark"] .bp_graph_options_popover,
html[data-bp-color-theme="dark"] .bp_group_hover_preview {
  background: rgba(15, 23, 42, 0.98);
}

html[data-bp-color-theme="dark"] .bp_graph_canvas svg > g.graph > polygon {
  fill: #0b1120;
  stroke: #0b1120;
}

html[data-bp-color-theme="dark"] .bp_graph_canvas svg g.edge path {
  stroke: #94a3b8;
}

html[data-bp-color-theme="dark"] .bp_graph_canvas svg g.edge polygon {
  fill: #94a3b8;
  stroke: #94a3b8;
}

html[data-bp-color-theme="dark"][data-bp-style="blueprint"] .bp_graph_legend_item {
  color: var(--bp-color-text);
}
"##⟩

private def readerJsTemplate : String := r##"
(function () {
  "use strict";

  const showFidelity = __SHOW_FIDELITY__;
  const repositories = __REPOSITORIES__;
  const themeStorageKey = "verso-blueprint-color-theme";
  const root = document.documentElement;

  function normalizeTheme(theme) {
    return theme === "dark" ? "dark" : "light";
  }

  function savedTheme() {
    try {
      return normalizeTheme(localStorage.getItem(themeStorageKey));
    } catch (_error) {
      return "light";
    }
  }

  function applyTheme(theme, persist) {
    const normalized = normalizeTheme(theme);
    root.setAttribute("data-bp-color-theme", normalized);
    const select = document.getElementById("bp-color-theme-select");
    if (select instanceof HTMLSelectElement) select.value = normalized;
    if (!persist) return;
    try {
      localStorage.setItem(themeStorageKey, normalized);
    } catch (_error) {}
  }

  function installThemeControl() {
    if (document.getElementById("bp-color-theme-select")) return true;
    const host = document.getElementById("bp-style-switcher");
    if (!host) return false;

    const control = document.createElement("div");
    control.className = "bp-style-switcher-control";

    const label = document.createElement("label");
    label.setAttribute("for", "bp-color-theme-select");
    label.textContent = "Theme";

    const select = document.createElement("select");
    select.id = "bp-color-theme-select";

    [
      ["light", "Light"],
      ["dark", "Dark"]
    ].forEach(function (entry) {
      const option = document.createElement("option");
      option.value = entry[0];
      option.textContent = entry[1];
      select.appendChild(option);
    });

    select.value = root.getAttribute("data-bp-color-theme") || "light";
    select.addEventListener("change", function () {
      applyTheme(select.value, true);
    });

    control.appendChild(label);
    control.appendChild(select);
    host.appendChild(control);
    return true;
  }

  function installThemeControlWhenReady() {
    if (installThemeControl()) return;
    const observer = new MutationObserver(function () {
      if (installThemeControl()) observer.disconnect();
    });
    observer.observe(document.body, { childList: true, subtree: true });
    window.setTimeout(function () {
      observer.disconnect();
    }, 5000);
  }

  function applyFidelityProfile() {
    document.querySelectorAll(".bp_metadata_tag").forEach(function (tag) {
      if (!(tag.textContent || "").trim().startsWith("fidelity-")) return;
      if (showFidelity) {
        tag.classList.add("bp-fidelity-tag");
      } else {
        tag.remove();
      }
    });
    root.setAttribute("data-bp-profile", showFidelity ? "dev" : "release");
    root.setAttribute("data-bp-tags-ready", "true");
  }

  function collapseCodePanels() {
    document.querySelectorAll("details.bp_code_panel[open]").forEach(function (panel) {
      panel.removeAttribute("open");
    });
  }

  function encodedSourcePath(path) {
    return path.split("/").map(encodeURIComponent).join("/");
  }

  function sourceRootFor(path) {
    return repositories.find(function (repository) {
      return path.startsWith(repository.prefix);
    });
  }

  function declarationRanges(manifest) {
    const ranges = new Map();
    if (!manifest || !Array.isArray(manifest.previews)) return ranges;
    manifest.previews.forEach(function (preview) {
      const declarations =
        preview && preview.codeData && preview.codeData.external
          ? preview.codeData.external.decls
          : null;
      if (!Array.isArray(declarations)) return;
      declarations.forEach(function (declaration) {
        if (declaration && declaration.canonical) {
          ranges.set(declaration.canonical, declaration.range || null);
        }
      });
    });
    return ranges;
  }

  function sourceAnchor(range) {
    if (!range || !Array.isArray(range.pos) || !Array.isArray(range.endPos)) {
      return { fragment: "", suffix: "" };
    }
    const start = Number(range.pos[0]) + 1;
    const end = Number(range.endPos[0]) + 1;
    if (!Number.isFinite(start) || !Number.isFinite(end)) {
      return { fragment: "", suffix: "" };
    }
    return {
      fragment: end > start ? "#L" + start + "-L" + end : "#L" + start,
      suffix: ":L" + start
    };
  }

  function linkDeclarationSources(ranges) {
    document
      .querySelectorAll(".bp_external_decl_rendered .declaration[data-decl]")
      .forEach(function (declaration) {
        const sourcePath = declaration.querySelector(".bp_external_decl_source_path");
        if (!sourcePath) return;
        const source = sourcePath.closest(".bp_external_decl_source");
        if (!source || source.querySelector(".bp_external_decl_source_link")) return;

        const path = (sourcePath.textContent || "").trim();
        const repository = sourceRootFor(path);
        if (!repository) return;

        const canonical = declaration.getAttribute("data-decl") || "";
        const anchor = sourceAnchor(ranges.get(canonical));
        const link = document.createElement("a");
        link.className = "bp_external_decl_source_link";
        link.href =
          repository.sourceRoot + encodedSourcePath(path) + anchor.fragment;
        link.target = "_blank";
        link.rel = "noopener noreferrer";
        link.title = "Open " + canonical + " in its GitHub source";

        const action = document.createElement("span");
        action.className = "bp_external_decl_source_action";
        action.textContent = "View source on GitHub ↗";

        const location = document.createElement("code");
        location.className = "bp_external_decl_source_location";
        location.textContent = path + anchor.suffix;

        link.appendChild(action);
        link.appendChild(location);
        source.replaceChildren(link);
      });
  }

  async function installSourceLinks() {
    try {
      const manifestUrl = new URL(
        "-verso-data/blueprint-manifest.json",
        document.baseURI
      );
      const response = await fetch(manifestUrl);
      if (!response.ok) return;
      linkDeclarationSources(declarationRanges(await response.json()));
    } catch (_error) {}
  }

  applyTheme(savedTheme(), false);
  document.addEventListener("DOMContentLoaded", function () {
    applyTheme(savedTheme(), false);
    collapseCodePanels();
    applyFidelityProfile();
    installSourceLinks();
    installThemeControlWhenReady();
  });
})();
"##

private def SourceRepository.toJson (repository : SourceRepository) : Lean.Json :=
  .mkObj [
    ("prefix", .str repository.pathPrefix),
    ("sourceRoot", .str repository.sourceRoot)
  ]

private def repositoriesJson (repositories : Array SourceRepository) : String :=
  Lean.Json.compress <| .arr <| repositories.map SourceRepository.toJson

/-- Reader JavaScript specialized to one build profile and its source repositories. -/
def readerJs (profile : Profile) (repositories : Array SourceRepository) : JS :=
  ⟨readerJsTemplate
    |>.replace "__SHOW_FIDELITY__" (if profile == .dev then "true" else "false")
    |>.replace "__REPOSITORIES__" (repositoriesJson repositories)⟩

/-- HTML configuration shared by the published Blueprint volumes. -/
def renderConfig (profile : Profile) (repositories : Array SourceRepository) : RenderConfig :=
  let config : RenderConfig := {}
  let htmlConfig := config.toHtmlConfig
  let htmlAssets := htmlConfig.toHtmlAssets
  { config with
    toHtmlConfig := { htmlConfig with
      toHtmlAssets := {
        htmlAssets with
        extraCss := htmlAssets.extraCss.insert readerCss
        extraJs := htmlAssets.extraJs.insert (readerJs profile repositories)
      }
    }
  }

end BlueprintSite
