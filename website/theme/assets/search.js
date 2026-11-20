(() => {
  const input = document.querySelector("#query");
  const results = document.querySelector("#search-results");
  const status = document.querySelector("#search-status");
  const directory = document.querySelector("#search-directory");
  const root = new URL(document.body.dataset.root + "/", location.href);
  const entries = (window.ITPEvalSearch || []).filter(e => !e.location.startsWith("search/"));
  const pageTitles = new Map(entries.filter(e => !e.location.includes("#")).map(e => [e.location, e.title]));
  const stop = new Set("a an and are can do does for how i in is it my of on the to use what where with".split(" "));
  const aliases = { mac: "macos", osx: "macos", win: "windows", coq: "rocq",
    installing: "install", installation: "install", libraries: "library",
    proofs: "proof", provers: "prover" };
  const texSymbols = { forall: "∀", exists: "∃", in: "∈", lor: "∨", land: "∧", to: "→", rightarrow: "→" };

  function normalize(text) {
    const tokens = text.replace(/\\(forall|exists|in|lor|land|to|rightarrow)\b/g, (_, name) => texSymbols[name])
      .toLowerCase().normalize("NFKD").replace(/\p{M}/gu, "")
      .match(/[\p{L}\p{N}]+|[\p{Sm}]/gu) || [];
    return tokens.map(t => aliases[t] || t).join(" ");
  }

  const records = entries.map(entry => {
    const [page] = entry.location.split("#");
    return { entry, page, title: normalize(entry.title), section: entry.location.includes("#"),
      parent: normalize(pageTitles.get(page) || ""), body: normalize(entry.text) };
  });

  function render() {
    const term = normalize(input.value);
    const allWords = [...new Set(term.split(" ").filter(Boolean))];
    const keywords = allWords.filter(w => !stop.has(w));
    const words = keywords.length ? keywords : allWords;
    results.replaceChildren();
    directory.hidden = Boolean(words.length && records.length);
    if (!records.length || !words.length) {
      status.textContent = records.length ? "" : "The full-text index is unavailable. Browse the pages below.";
      return;
    }
    const matches = [];
    for (const record of records) {
      const { title, body, parent, page, section } = record;
      let score = 0;
      for (const word of words) {
        if (title.split(" ").includes(word)) score += 14;
        else if (title.includes(word)) score += 9;
        else if (parent.includes(word) || page.includes(word)) score += 5;
        else if (body.includes(word)) score += 1;
        else { score = 0; break; }
      }
      if (!score) continue;
      if (title === term) score += 50;
      if (title.includes(term)) score += 10;
      if (section) score += 2;
      matches.push({ record, score });
    }
    matches.sort((a, b) => b.score - a.score);
    const shown = new Set();
    for (const { record: { entry, page } } of matches) {
      // MkDocs indexes both the page and its identical first heading.
      const key = page + "|" + normalize(entry.title);
      if (shown.has(key)) continue;
      shown.add(key);
      const link = document.createElement("a");
      link.href = new URL(entry.location || "./", root);
      const title = document.createElement("strong");
      title.textContent = entry.title;
      const prover = page.match(/^provers\/([^/]+)\//);
      if (prover && document.querySelector('[data-prover="' + prover[1] + '"]')) title.dataset.prover = prover[1];
      link.append(title);
      const parent = pageTitles.get(page) || "Overview";
      if (entry.title !== parent) {
        const path = document.createElement("small");
        path.textContent = parent;
        link.append(path);
      }
      const source = entry.text.replace(/\s+/g, " ").trim();
      if (source) {
        const snippet = document.createElement("span");
        snippet.className = "result-snippet";
        // Keep TeX expressions intact and end the excerpt on a word boundary.
        const chunks = source.match(/\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\]|\S+/g) || [];
        let length = 0;
        for (const word of chunks) {
          if (length > 160) { snippet.append("…"); break; }
          if (length) snippet.append(" ");
          if (word.startsWith("\\(") || word.startsWith("\\[")) {
            const math = document.createElement("span");
            window.katex.render(word.slice(2, -2), math, { throwOnError: false });
            snippet.append(math);
          } else snippet.append(word);
          length += word.length + 1;
        }
        link.append(snippet);
      }
      results.append(link);
    }
    const count = shown.size;
    status.textContent = count ? count + (count === 1 ? " result" : " results") : "No results. Try a prover, library name, or API function.";
  }

  function update() {
    const url = new URL(location.href);
    if (input.value) url.searchParams.set("q", input.value);
    else url.searchParams.delete("q");
    if (location.protocol !== "file:") history.replaceState(null, "", url);
    render();
  }
  function restore() {
    input.value = new URL(location.href).searchParams.get("q") || "";
    render();
  }
  input.addEventListener("input", update);
  input.form.addEventListener("submit", event => { event.preventDefault(); update(); results.querySelector("a")?.focus(); });
  input.addEventListener("keydown", event => {
    if (event.key === "ArrowDown" && results.firstElementChild) { event.preventDefault(); results.firstElementChild.focus(); }
  });
  results.addEventListener("keydown", event => {
    if (event.key !== "ArrowDown" && event.key !== "ArrowUp") return;
    event.preventDefault();
    const row = event.target.closest("a");
    const next = event.key === "ArrowUp" ? row.previousElementSibling || input : row.nextElementSibling || row;
    next.focus();
  });
  window.addEventListener("pageshow", restore);
  restore();
})();
