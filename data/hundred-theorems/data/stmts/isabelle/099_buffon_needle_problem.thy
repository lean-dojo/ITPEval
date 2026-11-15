(*
  File:    Buffons_Needle.thy
  Author:  Manuel Eberl <manuel@pruvisto.org>

  A formal solution of Buffon's needle problem.
*)
section \<open>Buffon's Needle Problem\<close>
theory Buffons_Needle
  imports "HOL-Probability.Probability"
begin

subsection \<open>Auxiliary material\<close>

lemma sin_le_zero': "sin x \<le> 0" if "x \<ge> -pi" "x \<le> 0" for x
  by sorry


subsection \<open>Problem definition\<close>

text \<open>
  Consider a needle of length $l$ whose centre has the $x$-coordinate $x$. The following then
  defines the set of all $x$-coordinates that the needle covers 
  (i.e. the projection of the needle onto the $x$-axis.)
\<close>
definition needle :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real set" where
  "needle l x \<phi> = closed_segment (x - l / 2 * sin \<phi>) (x + l / 2 * sin \<phi>)"

text_raw \<open>
\begin{figure}
\begin{center}
\begin{tikzpicture}
\coordinate (lefttick) at (-3,0);
\coordinate (righttick) at (3,0);

\draw (lefttick) -- (righttick);
\draw [thick] (lefttick) ++ (0,0.4) -- ++(0,3);
\draw [thick] (righttick) ++ (0,0.4) -- ++(0,3);

\coordinate (needle) at (1,2);

\newcommand{\needleangle}{55}
\newcommand{\needlelength}{{1}}
\newcommand{\needlethickness}{0.6pt}

\draw ($(lefttick)+(0,4pt)$) -- ($(lefttick)-(0,4pt)$);
\draw ($(righttick)+(0,4pt)$) -- ($(righttick)-(0,4pt)$);
\draw (0,4pt) -- (0,-4pt);

\draw [densely dashed, thin] let \p1 = (needle) in (\x1, 0) -- (needle);
\draw [densely dashed, thin] let \p1 = (needle) in (needle) -- (3, \y1);
\draw (needle) ++ (15pt,0) arc(0:\needleangle:15pt);
\path (needle) -- ++(15pt,0) node [above, midway, yshift=-1.9pt, xshift=1.8pt] {$\scriptstyle\varphi$};

\node [below, xshift=-3.5pt] at ($(lefttick)-(0,4pt)$) {$-\nicefrac{d}{2}$};
\node [below] at ($(righttick)-(0,4pt)$) {$\nicefrac{d}{2}$};
\node [below,yshift=-1pt] at (0,-4pt) {$0$};
\node [below,yshift=-2pt] at (needle |- 0,-4pt) {$x$};

\draw[<->] (needle) ++({\needleangle+90}:5pt) ++(\needleangle:{-\needlelength}) -- ++(\needleangle:2) node [midway, above, rotate=\needleangle] {$\scriptstyle l$};

\draw [line width=0.7pt,fill=white] (needle) ++({\needleangle+90}:\needlethickness) -- ++(\needleangle:\needlelength) arc({\needleangle+90}:{\needleangle-90}:\needlethickness) 
  -- ++(\needleangle:-\needlelength) -- ++(\needleangle:-\needlelength) arc({\needleangle+270}:{\needleangle+90}:\needlethickness) -- ++(\needleangle:\needlelength);

\end{tikzpicture}
\end{center}
\caption{A sketch of the situation in Buffon's needle experiment. There is a needle of length $l$
with its centre at a certain $x$ coordinate, angled at an angle $\varphi$ off the horizontal axis.
The two vertical lines are a distance of $d$ apart, each being $\nicefrac{d}{2}$ away from the
origin.}
\label{fig:buffon}
\end{figure}

\definecolor{myred}{HTML}{cc2428}
\begin{figure}[h]
\begin{center}
\begin{tikzpicture}
  \begin{axis}[
          xmin=0, xmax=7, ymin=0, ymax=1,
          width=\textwidth, height=0.6\textwidth,
          xlabel={$l/d$}, ylabel={$\mathcal P$}, tick style={thin,black},
          ylabel style = {rotate=270,anchor=west},
  ] 
  \addplot [color=myred, line width=1pt, mark=none,domain=0:1,samples=200] ({x}, {2/pi*x}); 
  \addplot [color=myred, line width=1pt, mark=none,domain=1:7,samples=200] ({x}, {2/pi*(x-sqrt(x*x-1)+acos(1/x)/180*pi)}); 
  \end{axis}
\end{tikzpicture}
\caption{The probability $\mathcal P$ of the needle hitting one of the lines, as a function of the quotient $l/d$ (where $l$ is the length of the needle and $d$ the horizontal distance between the lines).}
\label{fig:buffonplot}
\end{center}
\end{figure}
\<close>

text \<open>
  Buffon's Needle problem is then this: Assuming the needle's $x$ position is chosen uniformly
  at random in a strip of width $d$ centred at the origin, what is the probability that the 
  needle crosses at least one of the left/right boundaries of that strip (located at 
  $x = \pm\frac{1}{2}d$)?

  We will show that, if we let $x := \nicefrac{l}{d}$, the probability of this is
  \[
  \mathcal P_{l,d} =
    \begin{cases}
      \nicefrac{2}{\pi} \cdot x & \text{if}\ l \leq d\\
      \nicefrac{2}{\pi}\cdot(x - \sqrt{x^2 - 1} + \arccos (\nicefrac{1}{x})) & \text{if}\ l \geq d
    \end{cases} 
  \]
  A plot of this function can be found in Figure~\ref{fig:buffonplot}.
\<close>

locale Buffon =
  fixes d l :: real
  assumes d: "d > 0" and l: "l > 0"
begin

definition Buffon :: "(real \<times> real) measure" where
  "Buffon = uniform_measure lborel ({-d/2..d/2} \<times> {-pi..pi})"

lemma space_Buffon [simp]: "space Buffon = UNIV"
  by sorry

definition Buffon_set :: "(real \<times> real) set" where
  "Buffon_set = {(x,\<phi>) \<in> {-d/2..d/2} \<times> {-pi..pi}. needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}}"


subsection \<open>Derivation of the solution\<close>

text \<open>
  The following form is a bit easier to handle.
\<close>
lemma Buffon_set_altdef1:
  "Buffon_set =
     {(x,\<phi>) \<in> {-d/2..d/2} \<times> {-pi..pi}.
         let a = x - l / 2 * sin \<phi>; b = x + l / 2 * sin \<phi>
         in  min a b + d/2 \<le> 0 \<and> max a b + d/2 \<ge> 0 \<or> min a b - d/2 \<le> 0 \<and> max a b - d/2 \<ge> 0}"
  by sorry

lemma Buffon_set_altdef2:
  "Buffon_set = {(x,\<phi>) \<in> {-d/2..d/2} \<times> {-pi..pi}. abs x \<ge> d / 2 - abs (sin \<phi>) * l / 2}"
  by sorry
  
    
text \<open>
  By using the symmetry inherent in the problem, we can reduce the problem to the following 
  set, which corresponds to one quadrant of the original set:
\<close>
definition Buffon_set' :: "(real \<times> real) set" where
  "Buffon_set' = {(x,\<phi>) \<in> {0..d/2} \<times> {0..pi}. x \<ge> d / 2 - sin \<phi> * l / 2}"

lemma closed_buffon_set [simp, intro, measurable]: "closed Buffon_set"
  by sorry

lemma closed_buffon_set' [simp, intro, measurable]: "closed Buffon_set'"
  by sorry

lemma measurable_buffon_set [measurable]: "Buffon_set \<in> sets borel" 
  by sorry

lemma measurable_buffon_set' [measurable]: "Buffon_set' \<in> sets borel" 
  by sorry


sublocale prob_space Buffon
  unfolding Buffon_def
proof -
  have "emeasure lborel ({- d / 2..d / 2} \<times> {- pi..pi}) = ennreal (2 * d * pi)"
    unfolding lborel_prod [symmetric] using d
    by (subst lborel.emeasure_pair_measure_Times)
       (auto simp: ennreal_mult mult_ac simp flip: ennreal_numeral)
  also have "\<dots> \<noteq> 0 \<and> \<dots> \<noteq> \<infinity>"
    using d by auto
  finally show "prob_space (uniform_measure lborel ({- d / 2..d / 2} \<times> {- pi..pi}))"
    by (intro prob_space_uniform_measure) auto
qed

lemma buffon_prob_aux:
  "emeasure Buffon {(x,\<phi>). needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}} =
     emeasure lborel Buffon_set / ennreal (2 * d * pi)"
  by sorry

lemma emeasure_buffon_set_conv_buffon_set':
  "emeasure lborel Buffon_set = 4 * emeasure lborel Buffon_set'"
  by sorry

text \<open>
  It only remains now to compute the measure of @{const Buffon_set'}. We first reduce this
  problem to a relatively simple integral:
\<close>
lemma emeasure_buffon_set':
  "emeasure lborel Buffon_set' = 
     ennreal (integral {0..pi} (\<lambda>x. min (d / 2) (sin x * l / 2)))"
  (is "emeasure lborel ?A = _")
  by sorry

  
text \<open>
  We now have to distinguish two cases: The first and easier one is that where the length 
  of the needle, $l$, is less than or equal to the strip width, $d$:
\<close>
context
  assumes l_le_d: "l \<le> d"
begin

lemma emeasure_buffon_set'_short: "emeasure lborel Buffon_set' = ennreal l"
  by sorry

lemma emeasure_buffon_set_short: "emeasure lborel Buffon_set = 4 * ennreal l"
  by sorry

lemma prob_short_aux:
  "Buffon {(x, \<phi>). needle l x \<phi> \<inter> {- d / 2, d / 2} \<noteq> {}} = ennreal (2 * l / (d * pi))"
  by sorry

lemma prob_short: "\<P>((x,\<phi>) in Buffon. needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}) = 2 * l / (d * pi)"
  by sorry

end


text \<open>
  The other case where the needle is at least as long as the strip width is more complicated:
\<close>
context
  assumes l_ge_d: "l \<ge> d"
begin

lemma emeasure_buffon_set'_long: 
  shows "l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d \<ge> 0"
  and   "emeasure lborel Buffon_set' =
           ennreal (l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d)"
  by sorry

lemma emeasure_set_long: "emeasure lborel Buffon_set = 
        4 * ennreal (l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d)"
  by sorry

lemma prob_long_aux: 
  shows "2 / pi * ((l / d) - sqrt ((l / d)\<^sup>2 - 1) + arccos (d / l)) \<ge> 0"
  and   "Buffon {(x, \<phi>). needle l x \<phi> \<inter> {- d / 2, d / 2} \<noteq> {}} = 
           ennreal (2 / pi * ((l / d) - sqrt ((l / d)\<^sup>2 - 1) + arccos (d / l)))"
  by sorry

lemma prob_long:
  "\<P>((x,\<phi>) in Buffon. needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}) =
     2 / pi * ((l / d) - sqrt ((l / d)\<^sup>2 - 1) + arccos (d / l))"
  by sorry

end

theorem prob_eq:
  defines "x \<equiv> l / d"
  shows   "\<P>((x,\<phi>) in Buffon. needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}) =
             (if l \<le> d then
                2 / pi * x
              else
                2 / pi * (x - sqrt (x\<^sup>2 - 1) + arccos (1 / x)))"
  by sorry

end

end