// Arithmatex preserves TeX in Markdown. The same renderer also handles theme HTML.
(() => {
  const environments = ["equation", "align", "alignat", "gather", "equation*", "align*", "alignat*", "gather*", "CD"];
  const options = {
    delimiters: [
      { left: "$$", right: "$$", display: true },
      { left: "$", right: "$", display: false },
      { left: "\\(", right: "\\)", display: false },
      { left: "\\[", right: "\\]", display: true },
      ...environments.map(name => ({ left: "\\begin{" + name + "}", right: "\\end{" + name + "}", display: true })),
    ],
    ignoredClasses: ["katex", "codehilite"],
    throwOnError: false, trust: false,
  };
  window.renderITPEvalMath = el => renderMathInElement(el, options);
  window.renderITPEvalMath(document.body);
})();
