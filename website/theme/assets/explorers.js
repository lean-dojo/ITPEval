(() => {
  const root = new URL(document.body.dataset.root, location.href);
  async function load(name) {
    const response = await fetch(new URL("assets/" + name + ".json", root));
    if (!response.ok) throw new Error("Could not load " + name);
    return response.json();
  }

  const proof = document.querySelector(".proof-explorer");
  if (proof) load("proof-exercises").then(examples => {
    const prover = proof.querySelector('[name="prover"]');
    const candidate = proof.querySelector('[name="candidate"]');
    const file = proof.querySelector(".exercise-file");
    const before = proof.querySelector(".source-before");
    const fragment = proof.querySelector("mark");
    const after = proof.querySelector(".source-after");
    const feedback = proof.querySelector(".proof-feedback");
    const evidence = proof.querySelector(".exercise-evidence");
    const guide = proof.querySelector(".exercise-guide");

    function currentExample() {
      return examples[prover?.value || proof.dataset.exercise];
    }
    function showEdit() {
      fragment.textContent = candidate.value;
      feedback.textContent = "";
      delete feedback.dataset.verdict;
    }
    function showFile() {
      const example = currentExample();
      candidate.replaceChildren(...example.attempts.map(attempt =>
        new Option(attempt.candidate, attempt.candidate)
      ));
      file.textContent = example.entrypoint;
      file.dataset.prover = prover?.value || proof.dataset.exercise;
      before.textContent = example.before;
      after.textContent = example.after;
      guide.href = proof.dataset.guideBase + file.dataset.prover + "/#proof-completion";
      guide.hidden = !prover;
      evidence.href = new URL(example.evidence, root);
      showEdit();
    }
    proof.querySelector("button").addEventListener("click", () => {
      const attempt = currentExample().attempts[candidate.selectedIndex];
      const verdict = document.createElement("strong");
      verdict.textContent = attempt.verdict[0].toUpperCase() + attempt.verdict.slice(1);
      feedback.dataset.verdict = attempt.verdict;
      feedback.replaceChildren(verdict, " " + attempt.explanation.replaceAll("`", ""));
    });
    prover?.addEventListener("change", showFile);
    candidate.addEventListener("change", showEdit);
    showFile();
    proof.open = Boolean(prover);
    proof.hidden = false;
  }).catch(console.error);

  const timings = document.querySelector(".timing-explorer");
  if (timings) load("timing-comparison").then(measurements => {
    const prover = timings.querySelector("select");
    const times = [...timings.querySelectorAll("[data-time]")];
    const speedup = timings.querySelector("[data-speedup]");
    const seconds = new Intl.NumberFormat("en", { minimumFractionDigits: 3, maximumFractionDigits: 3 });
    const ratio = new Intl.NumberFormat("en", { maximumFractionDigits: 1 });
    function showTiming() {
      const row = measurements[prover.value];
      for (const field of times) {
        field.textContent = seconds.format(row[field.dataset.time]) + " s";
      }
      speedup.textContent = ratio.format(row.miss_s / row.hit_s) + "×";
    }
    prover.addEventListener("change", showTiming);
    showTiming();
    timings.hidden = false;
  }).catch(console.error);

  const scale = document.querySelector(".scale-explorer");
  if (scale) load("scale-comparison").then(measurements => {
    const prover = scale.querySelector("select");
    const count = scale.querySelector("[data-job-count]");
    const rates = [...scale.querySelectorAll("[data-throughput]")];
    const latency = scale.querySelector("[data-verdict-time]");
    const numbers = new Intl.NumberFormat("en", { maximumFractionDigits: 3 });
    function showScale() {
      const row = measurements[prover.value];
      count.textContent = numbers.format(row.jobs);
      for (const field of rates) {
        const trial = row.samples.find(sample => sample.workers === Number(field.dataset.throughput));
        field.textContent = numbers.format(trial.attempts_per_second) + " jobs/s";
      }
      const parallel = row.samples.find(sample => sample.workers === 4);
      latency.textContent = numbers.format(parallel.p95_time_to_verdict_s) + " s";
    }
    prover.addEventListener("change", showScale);
    showScale();
    scale.hidden = false;
  }).catch(console.error);
})();
