// Static pages export notebooks. The local preview can also run cells on its authenticated Jupyter kernel.
(() => {
  const local = ["127.0.0.1", "localhost", "[::1]"].includes(location.hostname)
    && document.cookie.split("; ").includes("itpeval_examples=local");
  const kernelSession = globalThis.crypto?.randomUUID?.() || String(Date.now());
  let kernel;
  let running = false;
  const languages = { bash: "Shell", sh: "Shell", shell: "Shell", python: "Python", json: "JSON", text: "Output", metamath: "Metamath", lean4: "Lean 4" };
  const cells = [];

  async function api(path, method, data) {
    const xsrf = document.cookie.split("; ").find(c => c.startsWith("_xsrf="))?.slice(6) || "";
    const response = await fetch("/api/kernels" + path, {
      method, credentials: "same-origin",
      headers: { "Content-Type": "application/json", "X-XSRFToken": decodeURIComponent(xsrf) },
      body: data ? JSON.stringify(data) : undefined,
    });
    if (!response.ok) {
      if ([401, 403].includes(response.status)) throw new Error("Sign in to your local Jupyter server to run this example.");
      throw new Error("Jupyter returned HTTP " + response.status + ".");
    }
    return response.status === 204 ? null : response.json();
  }

  const libraryClient = location.pathname.replace(/\/+$/, "").endsWith("/provers/lean4/mathlib-and-cslib");

  function pythonSource(lang, source) {
    if (libraryClient && lang === "lean4") {
      return `from pathlib import Path
from runpy import run_path
import tempfile
base = Path("build/lean-libraries")
if not (base / "toolchains/lean4/bin/lean").exists():
    raise RuntimeError("Run the two setup blocks on this page first.")
check_and_extract = run_path("examples/lean_libraries/run.py")["check_and_extract"]
with tempfile.TemporaryDirectory() as folder:
    project = Path(folder)
    (project / "Words.lean").write_text(${JSON.stringify(source)}, encoding="utf-8")
    check_and_extract(project, base / "cslib", base / "toolchains", base / "results")`;
    }
    if (languages[lang] === "Shell") return "%%bash\n" + source;
    if (lang === "metamath" || lang === "lean4") {
      return "from itpeval.itp import run_itp\nsource = " + JSON.stringify(source)
        + "\ncheck = run_itp(prover=" + JSON.stringify(lang) + ", code=source, mode='raw')"
        + "\nprint('Accepted' if check.ok else 'Rejected or unavailable')\nprint(check.stdout, check.stderr)";
    }
    return source;
  }

  async function execute(source, append) {
    kernel ??= await api("", "POST", { name: "python3" });
    const endpoint = new URL("/api/kernels/" + kernel.id + "/channels", location.origin);
    endpoint.protocol = location.protocol === "https:" ? "wss:" : "ws:";
    endpoint.searchParams.set("session_id", kernelSession);
    await new Promise((resolve, reject) => {
      const socket = new WebSocket(endpoint);
      const id = crypto.randomUUID();
      let finished = false;
      function finish(error) {
        if (finished) return;
        finished = true;
        socket.close();
        if (error) reject(error); else resolve();
      }
      socket.onopen = () => socket.send(JSON.stringify({
        header: { msg_id: id, username: "docs", session: kernelSession, date: new Date().toISOString(),
          msg_type: "execute_request", version: "5.3" },
        parent_header: {}, metadata: {}, channel: "shell", buffers: [],
        content: { code: source, silent: false, store_history: false, user_expressions: {},
          allow_stdin: false, stop_on_error: true },
      }));
      socket.onmessage = event => {
        if (typeof event.data !== "string") return;
        const msg = JSON.parse(event.data);
        if (msg.parent_header?.msg_id !== id) return;
        const c = msg.content;
        switch (msg.header.msg_type) {
          case "stream": append(c.text); break;
          case "execute_result": case "display_data":
            if (typeof c.data["text/latex"] === "string") append(c.data["text/latex"], true);
            else if (c.data["text/plain"]) append(c.data["text/plain"] + "\n");
            break;
          case "error": append(c.ename + ": " + c.evalue + "\n"); break;
          case "status": if (c.execution_state === "idle") finish(); break;
        }
      };
      socket.onclose = socket.onerror = () => {
        if (!finished) { kernel = undefined; finish(new Error("The kernel disconnected. Run the cell again to reconnect.")); }
      };
    });
  }

  function downloadNotebook() {
    const notebook = { nbformat: 4, nbformat_minor: 4,
      metadata: { kernelspec: { name: "python3", display_name: "Python 3", language: "python" } },
      cells: cells.map(({ lang, value, excerpt }) => {
        if (excerpt || lang === "text" || lang === "json")
          return { cell_type: "markdown", metadata: {}, source: "```" + lang + "\n" + value() + "\n```" };
        return { cell_type: "code", metadata: {}, source: pythonSource(lang, value()),
          execution_count: null, outputs: [] };
      }),
    };
    const url = URL.createObjectURL(new Blob([JSON.stringify(notebook, null, 2)], { type: "application/x-ipynb+json" }));
    const a = document.createElement("a");
    a.href = url;
    a.download = (location.pathname.split("/").filter(Boolean).pop() || "itpeval") + ".ipynb";
    a.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  for (const block of document.querySelectorAll(".codehilite")) {
    const pre = block.querySelector("pre");
    const code = pre?.querySelector("code");
    if (!code) continue;
    const lang = pre.dataset.language || [...block.classList].find(c => c.startsWith("language-"))?.slice(9) || "text";
    let original = code.textContent.replace(/\n$/, "");
    const listing = block.closest("figure.proof-listing");
    const bar = listing?.querySelector("figcaption") || document.createElement("div");
    bar.classList.add("cell-bar");
    const label = listing ? bar.querySelector("strong") : document.createElement("strong");
    if (!listing) {
      label.textContent = languages[lang] || lang;
      bar.append(label);
    }
    const output = document.createElement("div");
    output.className = "cell-output";
    output.hidden = true;
    output.setAttribute("aria-live", "polite");
    const editor = document.createElement("textarea");
    editor.className = "cell-editor";
    editor.setAttribute("aria-label", "Edit " + label.textContent + " example");
    editor.value = original;
    editor.rows = Math.min(20, Math.max(3, original.split("\n").length));
    editor.spellcheck = false;
    editor.hidden = true;
    const value = () => editor.value;
    cells.push({ lang, value, excerpt: Boolean(listing) });
    function button(text, fn) {
      const btn = document.createElement("button");
      btn.type = "button"; btn.textContent = text; btn.addEventListener("click", fn);
      bar.append(btn); return btn;
    }
    function showEditor(show) {
      pre.hidden = show; editor.hidden = !show;
      edit.textContent = show ? "Done" : "Edit";
      if (show) editor.focus();
      else if (editor.value !== original) code.textContent = editor.value;
      else code.innerHTML = highlighted;
    }
    let highlighted = code.innerHTML;
    let edit;
    if (!listing && lang !== "text") {
      edit = button("Edit", () => showEditor(editor.hidden));
      const reset = button("Reset", () => {
        editor.value = original; showEditor(false); output.hidden = true; reset.hidden = true;
      });
      reset.hidden = true;
      const controls = block.closest(".dataset-example")?.querySelector(".dataset-controls");
      if (controls) {
        const template = original;
        controls.hidden = false;
        controls.addEventListener("change", () => {
          const prover = controls.querySelector('[name="prover"]').value;
          const format = controls.querySelector('[name="format"]').value;
          original = template.replace("dataset metamath --output", "dataset " + prover + " --output")
            + (format === "parquet" ? " --format parquet" : "");
          code.textContent = original;
          highlighted = code.innerHTML;
          editor.value = original;
          showEditor(false);
          output.hidden = true;
          reset.hidden = true;
        });
      }
      editor.addEventListener("input", () => { reset.hidden = editor.value === original; });
    }
    const copy = button("Copy", async () => {
      try {
        await navigator.clipboard.writeText(value());
        copy.textContent = "Copied";
      } catch {
        if (edit) { showEditor(true); editor.select(); }
        else { const range = document.createRange(); range.selectNodeContents(code); const s = getSelection(); s.removeAllRanges(); s.addRange(range); }
        copy.textContent = "Text selected";
      }
      setTimeout(() => { copy.textContent = "Copy"; }, 1600);
    });
    if (listing) continue;
    if (lang === "lean4" && !libraryClient) {
      button("Lean Playground", () => {
        const link = "https://live.lean-lang.org/#code=" + encodeURIComponent(value());
        window.open(link, "_blank", "noopener,noreferrer");
      });
    }
    if (lang === "json") {
      button("Check JSON", () => {
        output.hidden = false;
        try { JSON.parse(value()); output.textContent = "Valid JSON"; }
        catch (error) { output.textContent = error.message; }
      });
    } else if (lang !== "text" && local) {
      const run = button("Run", async () => {
        if (running) return;
        running = true;
        document.querySelectorAll(".cell-run").forEach(b => b.disabled = true);
        output.hidden = false; output.textContent = "Starting…";
        stop.hidden = false;
        // Stream text as text nodes. Only an explicit Jupyter LaTeX result is typeset.
        let size = 0;
        try {
          await execute(pythonSource(lang, value()), (part, math = false) => {
            if (!size) output.replaceChildren();
            if (!part) return;
            const chunk = part.slice(-24000);
            let node;
            if (math) {
              node = document.createElement("span");
              const delimited = ["$", "\\(", "\\[", "\\begin{"].some(left => chunk.trimStart().startsWith(left));
              node.textContent = delimited ? chunk : "\\[" + chunk + "\\]";
              window.renderITPEvalMath(node);
            } else {
              node = document.createTextNode(chunk);
            }
            node.outputSize = chunk.length;
            output.append(node);
            size += chunk.length;
            while (size > 24000) {
              const first = output.firstChild;
              const excess = size - 24000;
              if (first.nodeType === Node.TEXT_NODE && first.outputSize > excess) {
                first.deleteData(0, excess);
                first.outputSize -= excess;
                size -= excess;
              } else {
                size -= first.outputSize;
                first.remove();
              }
            }
          });
          if (!size) output.textContent = "Finished.";
        } catch (error) {
          output.textContent = error.message;
          if (error.message.includes("Sign in")) {
            const a = document.createElement("a"); a.textContent = "Open local login";
            a.href = "/login?next=" + encodeURIComponent(location.pathname);
            output.append(" ", a);
          }
        } finally {
          running = false; stop.hidden = true;
          document.querySelectorAll(".cell-run").forEach(b => b.disabled = false);
        }
      });
      run.className = "cell-run";
      const stop = button("Stop", async () => {
        if (kernel) {
          try { await api("/" + kernel.id + "/interrupt", "POST"); }
          catch (error) { output.textContent = error.message; }
        }
      });
      stop.hidden = true;
      editor.addEventListener("keydown", e => {
        if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) { e.preventDefault(); run.click(); }
      });
    } else if (lang !== "text") {
      const notebook = button("Notebook", downloadNotebook);
      notebook.title = "Download this page’s examples for local Jupyter";
    }
    block.prepend(bar); pre.after(editor, output);
  }
})();
