(() => {
  const menu = document.getElementById("documentation-menu");
  const menuButton = document.querySelector(".menu-open");
  function revealCurrent(panel) {
    const link = panel?.querySelector('a[aria-current="page"]');
    if (!link || !panel.clientHeight) return;
    const end = link.getBoundingClientRect().bottom - panel.getBoundingClientRect().bottom;
    if (end > 0) panel.scrollTop += end + 8;
  }
  function setMenu(open) {
    menu.classList.toggle("menu-visible", open);
    menuButton.setAttribute("aria-expanded", String(open));
    menuButton.setAttribute(
      "aria-label",
      open ? "Close documentation menu" : "Open documentation menu",
    );
    if (open) revealCurrent(menu.querySelector(".doc-navigation"));
  }
  for (const button of document.querySelectorAll(".nav-toggle")) {
    const chapters = document.getElementById(button.getAttribute("aria-controls"));
    chapters.hidden = button.getAttribute("aria-expanded") === "false";
    button.hidden = false;
    button.addEventListener("click", () => {
      const open = chapters.hidden;
      chapters.hidden = !open;
      button.setAttribute("aria-expanded", String(open));
    });
  }
  revealCurrent(document.querySelector(".side"));
  menuButton.addEventListener("click", () => setMenu(!menu.classList.contains("menu-visible")));
  window
    .matchMedia("(max-width: 800px)")
    .addEventListener("change", (event) => {
      if (!event.matches) setMenu(false);
    });
  document.addEventListener("keydown", (event) => {
    const editing = event.target.matches(
      "input, textarea, [contenteditable=true]",
    );
    if (
      (event.key === "/" && !editing) ||
      ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === "k")
    ) {
      event.preventDefault();
      const input = document.querySelector("#query");
      if (input) { input.focus(); input.select(); }
      else document.querySelector(".search-open").click();
    } else if (event.key === "Escape" && menu.classList.contains("menu-visible")) {
      setMenu(false);
      menuButton.focus();
    }
  });

  for (const [index, group] of [...document.querySelectorAll(".interface-switch")].entries()) {
    const panels = [...group.querySelectorAll(".interface-panel")];
    const tabs = document.createElement("div");
    tabs.className = "interface-tabs";
    tabs.setAttribute("role", "tablist");
    tabs.setAttribute("aria-label", group.dataset.label || "Example interface");
    function activate(selected) {
      panels.forEach((panel, i) => {
        panel.hidden = selected !== i;
        const tab = tabs.children[i];
        tab.setAttribute("aria-selected", String(selected === i));
        tab.tabIndex = selected === i ? 0 : -1;
      });
    }
    panels.forEach((panel, i) => {
      const heading = panel.querySelector("h3");
      const tab = document.createElement("button");
      tab.textContent = heading.textContent;
      tab.id = `interface-${index}-tab-${i}`;
      panel.id = `interface-${index}-panel-${i}`;
      panel.setAttribute("role", "tabpanel");
      panel.setAttribute("aria-labelledby", tab.id);
      panel.tabIndex = 0;
      tab.type = "button";
      tab.setAttribute("role", "tab");
      tab.setAttribute("aria-controls", panel.id);
      // Preserve section anchors in the table of contents and search index.
      heading.classList.add("panel-heading");
      tab.addEventListener("click", () => activate(i));
      tab.addEventListener("keydown", event => {
        const next = { ArrowLeft: (i + panels.length - 1) % panels.length,
          ArrowRight: (i + 1) % panels.length, Home: 0, End: panels.length - 1 }[event.key];
        if (next === undefined) return;
        event.preventDefault(); activate(next); tabs.children[next].focus();
      });
      tabs.append(tab);
    });
    group.prepend(tabs);
    function revealAnchor() {
      const id = location.hash.slice(1);
      const panel = document.getElementById(id)?.closest(".interface-panel");
      if (panels.includes(panel)) { activate(panels.indexOf(panel)); group.scrollIntoView({ block: "nearest" }); }
    }
    const platform = navigator.userAgentData?.platform || navigator.platform;
    const preferred = group.dataset.label === "Operating system"
      ? panels.findIndex(panel => platform.toLowerCase().includes(panel.querySelector("h3").id.replace("macos", "mac").replace("windows", "win")))
      : 0;
    activate(Math.max(0, preferred));
    revealAnchor();
    window.addEventListener("hashchange", revealAnchor);
  }

  const film = document.querySelector("#library-film");
  if (film) {
    const select = document.querySelector("#film-chapter");
    const chapters = Array.from(select.options);
    const player = film.closest("figure");
    const play = player.querySelector(".film-play");
    const seek = player.querySelector(".film-seek");
    const time = player.querySelector(".film-time");
    const captions = player.querySelector(".film-captions");
    const full = player.querySelector(".film-full");
    const stamp = seconds => Math.floor(seconds / 60) + ":" + String(Math.floor(seconds % 60)).padStart(2, "0");
    function paintPlayback() {
      play.firstElementChild.textContent = film.paused ? "▶" : "Ⅱ";
      play.setAttribute("aria-label", (film.paused ? "Play" : "Pause") + " library tour");
    }
    function togglePlayback() {
      if (film.paused) film.play().catch(() => { film.controls = true; }); else film.pause();
    }
    play.addEventListener("click", togglePlayback);
    film.addEventListener("click", () => { if (!film.controls) togglePlayback(); });
    film.addEventListener("play", paintPlayback);
    film.addEventListener("pause", paintPlayback);
    function showDuration() {
      if (Number.isFinite(film.duration)) {
        seek.max = film.duration;
        seek.disabled = false;
        select.closest(".film-library").hidden = false;
        selectCurrent();
      }
    }
    film.addEventListener("loadedmetadata", showDuration);
    showDuration();
    seek.addEventListener("input", () => { film.currentTime = Number(seek.value); });
    captions.addEventListener("click", () => {
      const track = [...film.textTracks].find(t => t.kind === "captions");
      if (!track) return;
      const show = track.mode !== "showing";
      track.mode = show ? "showing" : "hidden";
      captions.setAttribute("aria-pressed", String(show));
      captions.setAttribute("aria-label", show ? "Hide captions" : "Show captions");
    });
    full.hidden = !document.fullscreenEnabled;
    full.addEventListener("click", () => film.requestFullscreen().catch(() => { film.controls = true; }));
    document.addEventListener("fullscreenchange", () => { film.controls = document.fullscreenElement === film; });
    film.controls = false;
    player.querySelector(".film-transport").hidden = false;
    function selectCurrent() {
      seek.value = film.currentTime;
      time.textContent = stamp(film.currentTime) + " / " + stamp(Number(seek.max));
      seek.setAttribute("aria-valuetext", stamp(film.currentTime) + " of " + stamp(Number(seek.max)));
      const chapter = chapters.filter(option => Number(option.dataset.start) <= film.currentTime).pop();
      select.value = chapter.value;
    }
    select.addEventListener("change", () => {
      const chapter = select.selectedOptions[0];
      film.currentTime = Number(chapter.dataset.start) + 0.05;
    });
    film.addEventListener("timeupdate", selectCurrent);
    film.addEventListener("seeked", selectCurrent);

    // Start silently on arrival. A visitor who prefers reduced motion can press Play.
    const motion = window.matchMedia("(prefers-reduced-motion: reduce)");
    if (!motion.matches) {
      film.autoplay = true;
      film.play().catch(paintPlayback);
    }
    motion.addEventListener("change", event => {
      if (event.matches) {
        film.autoplay = false;
        film.pause();
      }
    });
    paintPlayback();
  }
})();
