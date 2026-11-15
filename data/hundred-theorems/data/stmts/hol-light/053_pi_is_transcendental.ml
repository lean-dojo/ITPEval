(*

transcendence-20241221.ml
D. J. Bernstein

This file is hereby placed into the public domain.

SPDX-License-Identifier: LicenseRef-PD-hp OR CC0-1.0 OR 0BSD OR MIT-0 OR MIT

=====

To re-verify under Debian (about an hour depending on CPU):
  sudo apt install opam xdot -y
  time opam init github git+https://github.com/ocaml/opam-repository.git --disable-sandboxing -a
  time opam switch create 5.2.0
  time opam install 'hol_light=3.0.0' -y
  eval `opam env`
  time LINE_EDITOR=env hol.sh \
  < transcendence-20241221.ml \
  > transcendence-20241221.out &

=====

Highlighted theorems:

e_is_irrational (1744 Euler):
  ~(cexp (Cx (&1)) IN QinC)

e_is_transcendental (1873 Hermite):
  ~algebraic_number (cexp (Cx (&1)))

pi_is_transcendental (1882 Lindemann):
  ~algebraic_number (Cx pi)

transcendental_if_exp_nonzero_algebraic (1882 Lindemann):
  algebraic_number a
  /\ algebraic_number (cexp a)
  ==> a = Cx (&0)

zero_sum_algebraic_exp_algebraic (1882 Lindemann):
  forall S B.
    FINITE S /\
    S SUBSET algebraic_number /\
    (forall s. s IN S ==> algebraic_number (B s)) /\
    ring_sum complex_ring S (\s. B s * cexp s) = Cx (&0)
    ==> (forall s. s IN S ==> B s = Cx (&0))

Traditional Greek presentation of the last theorem:
if sum_α β_α exp α = 0,
where each α is algebraic and each β_α is algebraic,
then each β_α = 0.
This easily implies the other highlighted theorems.

Some of the proofs below act as sanity checks on the definitions
(e.g., algebraic_number_QinC; algebraic_number_ii).
Another sanity check would be to prove that,
for reals, the definition of algebraic numbers here
is equivalent to the definition in 100/liouville.ml,
which internally uses real polys defined via Library/poly.html
with polys constrained to have integer coefficients.

=====

Historical notes:

Various sources attribute the last theorem to 1885 Weierstrass
as the "Lindemann--Weierstrass theorem",
or sometimes the "Hermite--Lindemann--Weierstrass theorem".
My reading of the Lindemann and Weierstrass papers is that
Lindemann had this theorem and Weierstrass was, with Lindemann's agreement,
just giving a more detailed exposition of the result,
not assuming so much reader familiarity with 1873 Hermite.

Baker's book refers to the second result as "Lindemann's theorem",
saying that Lindemann sketched the proof
and that Weierstrass gave a rigorous proof.
I don't know what's supposedly missing from the sketch.

Some sources instead claim that this theorem is a simplification due to Baker
of the original "Lindemann--Weierstrass theorem",
namely the statement that if α_1,... are algebraic numbers
linearly independent over \Q
then exp(α_1),... are algebraically independent over \Q.
No evident signs of anyone asking the obvious questions:
"Um, are we sure that people didn't find this theorem first,
with the algebraic-independence version as a corollary later?
Maybe we should check what Lindemann actually wrote?"

=====

Proof notes:

The high-level structure of the proofs here
follows Lindemann and most of the literature
in symmetrizing β to reduce to the case that β_α is rational,
and symmetrizing α to reduce further to the core case that
β_α is rational and invariant under conjugation of α.

The first major proof stage is the core proof,
producing transcendence_all_0_QinC here:
if sum_α β_α exp α = 0,
where each α is algebraic, each β_α is rational,
and β_α is invariant under conjugation of α,
then each β_α = 0.

The core proof here follows 1990 Beukers--Bezivin--Robba.
Most of the literature instead follows 1893 Hilbert.

The core proof here uses polynomial reversals.
Laurent series would avoid this but would need more infrastructure.

For eventually optimizing an explicit form of the transcendence proof
(proving a lower bound on weighted sum of exp of algebraic numbers),
one wants an explicit lower bound on factorials,
such as factorial_lower_bound here (which says (n/e)^n <= n!).
More work (as in, e.g., 100/stirling.ml)
produces only marginally better bounds.

For the current target of just saying sum of exp of algebraic is nonzero,
it suffices to say that factorials eventually beat any exponential.
This doesn't need the explicit bound, but isn't much simpler,
so the proof here uses the explicit bound.

The proofs of transcendence of e and pi here
are immediately after the first stage.
This is common in the literature:
it is a warmup for parts of the second stage,
and it gives proofs of those facts that are shorter overall
than deriving the facts after the second stage (or the third).

The pi proof here uses explicit resolvent identities,
proven via expformal and Newton's identities,
whereas all of the literature that I've found
instead uses the fundamental theorem of symmetric functions.

(Some sources credit Newton's identities to Girard.
I don't see the rationale for this credit.
1629 Girard had _formulas_ for first few coeffs in terms of power sums.
1707 Newton had a bilinear identity relating coeffs to power sums,
which can be used as a _recurrence_ for all coeffs given power sums.
One way to prove Girard's formulas is to iterate Newton's identities;
this doesn't mean that Girard published Newton's identities.)

The second major proof stage uses α symmetrization
to obtain zero_sum_QinC_exp_algebraic here:
if sum_α β_α exp α = 0,
where each α is algebraic and each β_α is rational,
then each β_α = 0.

Consider the product prod_q (sum_α β_α exp(q(α)))
where q runs through all permutations
of a finite Galois-stable set containing all α.
This product is 0: consider the identity permutation.
Expanding the product produces
a sum that fits the core case.
As in the literature, the proof here
uses the fundamental theorem of symmetric functions
(which is also proven here).
Applying the core theorem then shows that
sum_D ((prod β_α^(D_α)) #{f: sum_q q(f(q)) = z}) = 0
for each z, where f runs through functions with distribution D.
There is then a denouement concluding that β_α = 0 for each α.

The typical denouement in the literature
identifies the maximum z with nonzero prod β_α^(D_α),
where maximum refers to lex order on \C.
A different denouement appears in
1952 Steinberg--Redheffer "Analytic proof of the Lindemann theorem".
The denouement here follows 1952 Steinberg--Redheffer
but works with expformal to skip a detour through convergence.
The point is that, working backwards, one has
prod_q (sum_α β_α E(q(α))) = 0
and thus sum_α β_α E(q(α)) = 0 for some q,
for any function E mapping addition to multiplication in some field.
The 1952 proof considers E(α) = z^α for various complex z;
the proof here takes E = expformal.

The third major proof stage symmetrizes β,
producing zero_sum_algebraic_exp_algebraic here:
if sum_α β_α exp α = 0,
where each α is algebraic and each β_α is algebraic,
then each β_α = 0.

For β symmetrization, analogously to α symmetrization,
the proof here follows the literature
in using the fundamental theorem of symmetric functions,
but again uses a simplified version of the 1952 denouement.

As in, e.g., 2017 Bernard, the β symmetrization here
works with one polynomial having all β as roots,
rather than separately symmetrizing each β.
The shortest-for-papers symmetrization approach
(used in, e.g., 1990 Beukers--Bezivin--Robba)
picks a finite-degree Galois extension of \Q containing all α and all β
and then applies all automorphisms of the extension
to symmetrize all α and β simultaneously,
but this relies on more background.

The proof here of transcendental_if_exp_nonzero_algebraic
is immediately after the second stage.
This is common in the literature.
Waiting until after the third stage
would replace the minpoly over \Q in this proof
with a linear poly over \Qbar,
giving a slightly shorter last step of the proof
but again longer proofs overall.
Computationally, the β symmetrization,
if optimized, would give back the same minpoly over \Q.

=====

Prerequisite notes:

The big import of Multivariate/cauchy.ml
is for the fundamental theorem of algebra (FTA).
This also brings in various complex-number basics,
the complex exponential function (cexp),
and a bound on the tail of the exp series (TAYLOR_CEXP).

Most proofs of Lindemann's theorem have bigger analytic parts,
for example to put bounds on integrals.
The proof here focuses more on identities of formal power series.

*)

(* ===== imports *)

needs "Library/products.ml";;
needs "Library/ringtheory.ml";;
needs "Multivariate/cauchy.ml";;

prioritize_real();; (* to ensure portability *)

(* ===== tactics *)

let rw = REWRITE_TAC;;
let once_rw = ONCE_REWRITE_TAC;;
let qed = ASM_MESON_TAC;;
let simp = ASM_SIMP_TAC;;
let simporqed = (simp[] THEN qed[]) ORELSE (simp[]);;
let pass = ALL_TAC;;
let case = ASM_CASES_TAC;;
let conjunction = CONJ_TAC;;
let splitiff = EQ_TAC;;
let know = ASSUME;;

let sufficesby_bare x = MATCH_MP_TAC x;;
let sufficesby x = sufficesby_bare(REWRITE_RULE[GSYM IMP_CONJ] x);;
let intro = REPEAT STRIP_TAC;;
let intro_genonly = REPEAT GEN_TAC;;
let intro_gendisch = REPEAT GEN_TAC THEN REPEAT DISCH_TAC;;
let subgoal t = SUBGOAL_THEN t ASSUME_TAC;;
let witness = EXISTS_TAC;;

let proven_if t why = case t THENL
[qed why;
  pass];;

let labelhavetac L t tac = SUBGOAL_THEN t MP_TAC THENL
[tac;
  pass] THEN
DISCH_THEN(fun th -> LABEL_TAC L th);;

let havetac = labelhavetac "";;

let labelhave L t why = labelhavetac L t(qed why);;

let have t why = havetac t(qed why);;
let have_rw t why = have t why THEN once_rw[know t];;

let labelspecialize L v th = LABEL_TAC L (UNDISCH_ALL (REWRITE_RULE [IMP_CONJ] (ISPECL v th)));;
let specialize = labelspecialize "";;
let specialize_assuming v th = ASSUME_TAC(REWRITE_RULE [IMP_CONJ] (ISPECL v th));;
let specialize_assuming_nosplit v th = ASSUME_TAC(UNDISCH_ALL(ISPECL v th));;

let specialize_forward v th = ASSUME_TAC(UNDISCH_ALL (fst (EQ_IMP_RULE (UNDISCH_ALL (REWRITE_RULE [IMP_CONJ] (ISPECL v th))))));;

let specialize_reverse v th = ASSUME_TAC(UNDISCH_ALL (snd (EQ_IMP_RULE (UNDISCH_ALL (REWRITE_RULE [IMP_CONJ] (ISPECL v th))))));;

let recall = specialize[];;
let complex_field_fact t = recall(COMPLEX_FIELD t);;
let real_field_fact t = recall(REAL_FIELD t);;
let real_linear_fact t = recall(REAL_ARITH t);;
let int_linear_fact t = recall(INT_ARITH t);;
let num_linear_fact t = recall(ARITH_RULE t);;
let set_fact_using t why = havetac t(SET_TAC why);;
let set_fact t = recall(SET_RULE t);;
let set_fact_assuming t = specialize_assuming[](SET_RULE t);;

let def n d = X_CHOOSE_TAC n(MESON [] (mk_exists (n, mk_eq (n, d))));;

let removelabeled L = REMOVE_THEN L (fun th -> ALL_TAC);;

let choose n p why =
  labelhave "choosetmp" (mk_exists (n, p)) why THEN
  X_CHOOSE_TAC n(UNDISCH (TAUT (mk_imp (mk_exists (n, p), mk_exists (n, p))))) THEN
  removelabeled "choosetmp";;

let choose2 n1 n2 p why =
  choose n1 (mk_exists (n2, p)) why THEN
  choose n2 p []
;;

(* ===== sets *)

let subset_y = `
  !S U:X->bool.
  S SUBSET U <=>
  (!y. y IN S ==> y IN U)
`;;

let extension_z = `
  !S:X->bool T.
  S = T <=>
  (!z. z IN S <=> z IN T)
`;;

let insert_delete_nonmember = `
  !(x:X) S.
  ~(x IN S) ==>
  (x INSERT S) DELETE x = S
`;;

let surjective_finite = `
  !f p:T->bool.
  (!t:T. ?s:S. f(s) = t) ==>
  FINITE {s | p(f(s))} ==>
  FINITE {t | p(t)}
`;;

let is_inters = `
  !(x:X->bool) u.
  x IN u /\
  (!s. s IN u ==> x SUBSET s) ==>
  x = INTERS u
`;;

let card_empty = `
  CARD ({}:X->bool) = 0
`;;

(* just to avoid SUC from CARD_CLAUSES *)
let card_insert = `
  !x:X S.
  FINITE S ==>
  CARD(x INSERT S)
  = (if x IN S then CARD S else CARD S + 1)
`;;

let subset_full_card = `
  !S:X->bool U.
  FINITE S ==>
  ( (U SUBSET S /\ CARD U = CARD S)
    <=> U = S
  )
`;;

let finite_subsets_card = `
  !S:X->bool n.
  FINITE S ==>
  FINITE {U | U SUBSET S /\ CARD U = n}
`;;

let subsets_full_card = `
  !S:X->bool.
  FINITE S ==>
  {U | U SUBSET S /\ CARD U = CARD S}
  = {S}
`;;

let subsets_card_0 = `
  !S:X->bool.
  FINITE S ==>
  {U | U SUBSET S /\ CARD U = 0}
  = {{}}
`;;

let subsets_full_card_empty = `
  {U:X->bool | U SUBSET {} /\ CARD U = 0}
  = {{}}
`;;

let subsets_card_toobig = `
  !S:X->bool n.
  FINITE S ==>
  ~(n <= CARD S) ==>
  {U | U SUBSET S /\ CARD U = n} = {}
`;;

let powerset_insert_disjoint = `
  !S:X->bool t.
  ~(t IN S) ==>
  DISJOINT
    {A | A SUBSET S}
    (IMAGE (\A. t INSERT A) {A | A SUBSET S})
`;;

let image_card_powerset = `
  !S:X->bool.
  FINITE S ==>
  IMAGE CARD {A | A SUBSET S} = (0..CARD S)
`;;

let le_lt_numseg = `
  !a b.
  {i:num | a <= i /\ i < b}
  = if a < b then (a..b-1) else {}
`;;

let finite_le_lt = `
  !a b.
  FINITE {i:num | a <= i /\ i < b}
`;;

(* warning: this is normal notation only if a<=b *)
let card_le_lt = `
  !a b.
  CARD {i:num | a <= i /\ i < b} = b-a
`;;

let insert_empty = `
  !x:X.
  x INSERT {} = {x}
`;;

let max_finite = `
  !S:num->bool.
  FINITE S ==>
  (
    S = {} \/
    (?m. m IN S /\ (!n. m < n ==> ~(n IN S)))
  )
`;;

let image_surj = `
  !f:X->Y A B.
  SURJ f A B ==>
  IMAGE f A = B
`;;

let elim_image_subset_u = `
  !A B f:X->Y.
  IMAGE f A SUBSET B <=>
  (!u. u IN A ==> f u IN B)
`;;

let elim_image_subset_v = `
  !A B f:X->Y.
  IMAGE f A SUBSET B <=>
  (!v. v IN A ==> f v IN B)
`;;

let select_foreach = `
  !S P.
  (!s:X. s IN S ==> ?t:Y. P s t) ==>
  (!s:X. s IN S ==> P s ((\s. @t. P s t) s))
`;;

(* XXX: there must be a better way to do renaming *)
let o_def_s = `
  !f:Y->Z g:X->Y.
  f o g = (\s. f (g s))
`;;

let in_image_cd = `
  !d s f:X->Y.
  d IN IMAGE f s <=>
  (?c. d = f c /\ c IN s)
`;;

let in_image_vw = `
  !w s f:X->Y.
  w IN IMAGE f s <=>
  (?v. w = f v /\ v IN s)
`;;

(* ===== pairs *)

let lambda_pair_ab = `
  !f:A#B->C.
  (\ab. f ab) = (\(a,b). f (a,b))
`;;

let injective_pair_rewrite = `
  !f:A#B->L.
  (!(a,b) (c,d). f (a,b) = f (c,d) ==> (a,b) = (c,d)) ==>
  !x y. f x = f y ==> x = y
`;;

let image_pair = `
  !P f:A->B->C.
  IMAGE (\(a,b). f a b) {a,b | P a b}
  = {f a b | P a b}
`;;

(* ===== functions *)

let functions = new_definition `
  functions (A:X->bool) (B:Y->bool)
  = {f | IMAGE f A SUBSET B /\ (!z. ~(z IN A) ==> f z = ARB)}
`;;

let in_functions = `
  !A:X->bool B:Y->bool f.
  f IN functions A B <=>
  IMAGE f A SUBSET B /\ (!z. ~(z IN A) ==> f z = ARB)
`;;

let fun_eq_thm_e = `
  !f g:X->Y.
  f = g <=> (!e. f e = g e)
`;;

let fun_eq_thm_v = `
  !f g:X->Y.
  f = g <=> (!v. f v = g v)
`;;

let image_functions_subset = `
  !A:X->bool B:Y->bool f.
  f IN functions A B ==>
  IMAGE f A SUBSET B
`;;

(* XXX: factor most image_functions_subset applications via this *)
let functions_to = `
  !A:X->bool B:Y->bool f x.
  f IN functions A B ==>
  x IN A ==>
  f x IN B
`;;

let finite_functions = `
  !A:X->bool B:Y->bool.
  FINITE A ==>
  FINITE B ==>
  FINITE (functions A B)
`;;

let functions_empty = `
  !B:Y->bool.
  functions {} B = {\x:X. ARB}
`;;

let functions_insert = `
  !A:X->bool B:Y->bool i:X.
  ~(i IN A) ==>
  functions (i INSERT A) B
  = IMAGE
      (\((b:Y),(f:X->Y)) (a:X). if a = i then b else f a)
      (B CROSS (functions A B))
`;;

let functions_insert_injective = `
  !A:X->bool B:Y->bool i:X v w.
  ~(i IN A) ==>
  v IN B CROSS functions A B ==>
  w IN B CROSS functions A B ==>
  (\((b:Y),(f:X->Y)) (a:X). if a = i then b else f a) v
  = (\((b:Y),(f:X->Y)) (a:X). if a = i then b else f a) w ==>
  v = w
`;;

(* ===== permutations *)

let perm = new_definition `
  perm (S:X->bool) (f:X->X)
  <=> f permutes S
`;;

let perm_in_permutes = `
  !S:X->bool f.
  perm S f <=> f IN {p | p permutes S}
`;;

let perm_set_permutes = `
  !S:X->bool.
  perm S = {p | p permutes S}
`;;

let card_perm = `
  !S:X->bool.
  FINITE S ==>
  CARD(perm S) = FACT(CARD S)
`;;

let finite_perm = `
  !S:X->bool.
  FINITE S ==>
  FINITE(perm S)
`;;

let permutes_o_inverse_refl_o = `
  !A:X->bool f:X->X g:Y->X.
  f permutes A ==>
  f o inverse f o g = g
`;;

let inverse_permutes_o_refl_o = `
  !A:X->bool f:X->X g:Y->X.
  f permutes A ==>
  inverse f o f o g = g
`;;

let image_permutes_o_perm = `
  !A:X->bool f:X->X.
  f permutes A ==>
  IMAGE (\i. f o i) (perm A) = perm A
`;;

let image_permutes_o_functions_perm = `
  !A:X->bool B:Y->bool f:X->X.
  f permutes A ==>
  IMAGE
    (\g i. g(f o i))
    (functions (perm A) B)
  = functions (perm A) B
`;;

let injective_permutes_arbo_functions = `
  !A:X->bool B:Y->bool p:Y->Y f g.
  p permutes B ==>
  f IN functions A B ==>
  g IN functions A B ==>
  (\a. if a IN A then p (f a) else ARB) =
  (\a. if a IN A then p (g a) else ARB) ==>
  f = g
`;;

let image_permutes_arbo_functions = `
  !A:X->bool B:Y->bool p:Y->Y.
  p permutes B ==>
  IMAGE (\ab a. if a IN A then p(ab a) else ARB)
    (functions A B)
  = functions A B
`;;

let injective_permutes_arbo_functions_functions = `
  !A:X->bool B:Y->bool C:Z->bool p:Y->Y f g.
  p permutes B ==>
  f IN functions (functions A B) C ==>
  g IN functions (functions A B) C ==>
  (\ab. if ab IN functions A B
        then f (\a. if a IN A then p (ab a) else ARB)
        else ARB) =
  (\ab. if ab IN functions A B
        then g (\a. if a IN A then p (ab a) else ARB)
        else ARB) ==>
  f = g
`;;

let image_permutes_arbo_functions_functions = `
  !A:X->bool B:Y->bool C:Z->bool p:Y->Y.
  p permutes B ==>
  IMAGE
    (\bc ab. if ab IN functions A B
             then bc(\a. if a IN A
                         then p(ab(a))
                         else ARB)
             else ARB)
    (functions (functions A B) C)
  = functions (functions A B) C
`;;

(* ===== naturals *)

let min_le = `
  !a b.
  MIN a b <= a
  /\ MIN a b <= b
`;;

let le_min = `
  !a b c.
  a <= MIN b c <=>
  a <= b /\ a <= c
`;;

let max_le = `
  !a b c.
  MAX a b <= c <=>
  a <= c /\ b <= c
`;;

let fact_1 = `
  FACT 1 = 1
`;;

let binom_stair_sum = `
  !e n.
  binom(n+e,e)
  = if e = 0 then 1 else nsum (0..n) (\a. binom(a+e-1,e-1))
`;;

(* simpler special case of NSUM_REFLECT *)
let nsum_reflect_0 = `
  !f n.
  nsum(0..n) f = nsum(0..n) (\i. f(n-i))
`;;

(* GEN `b` NSUM_DELTA modulo order of variables *)
let nsum_delta = `
  !s a:X b.
  nsum s (\x. if x = a then b else 0)
  = (if a IN s then b else 0)
`;;

let term_le_nsum = `
  !f S t:X.
  FINITE S ==>
  t IN S ==>
  f t <= nsum S f
`;;

let binom_reverse_stair_sum = `
  !e n.
  binom(n+e,e)
  = if e = 0 then 1 else
    nsum (0..n) (\a. binom(n-a+e-1,e-1))
`;;

let fact_binom_lemma_37 = `
  !n i.
  i < n ==>
  FACT(n-i) * binom(n,i) =
  (FACT(n-1-i) * binom(n-1,i)) +
  ((n-1) * FACT(n-1-i) * binom(n-1,i))
`;;

let properly_le = `
  properly (<=) = (<):num->num->bool
`;;

let o_permutes_subset = `
  !A S f:X->X.
  f permutes S ==>
  A SUBSET S ==>
  A o f SUBSET S
`;;

let image_permutes_subset = `
  !A S f:X->X.
  f permutes S ==>
  A SUBSET S ==>
  IMAGE f A SUBSET S
`;;

let image_inverse_permutes = `
  !A S f:X->X.
  f permutes S ==>
  A SUBSET S ==>
  IMAGE (inverse f) A = A o f
`;;

let image_o_permutes = `
  !A S f:X->X.
  f permutes S ==>
  A SUBSET S ==>
  IMAGE f (A o f) = A
`;;

let o_image_permutes = `
  !A S f:X->X.
  f permutes S ==>
  A SUBSET S ==>
  (IMAGE f A) o f = A
`;;

let card_image_permutes = `
  !A S f:X->X.
  f permutes S ==>
  A SUBSET S ==>
  FINITE A ==>
  CARD(IMAGE f A) = CARD A
`;;

let card_o_permutes = `
  !A S f:X->X.
  f permutes S ==>
  A SUBSET S ==>
  FINITE A ==>
  CARD(A o f) = CARD A
`;;

let o_permutes_cancel = `
  !S f:X->X g h:X->Y.
  f permutes S ==>
  g o f = h o f ==>
  g = h
`;;

(* ===== sets of naturals *)

let range = new_definition `
  range = (>):num->num->bool
`;;

let range_lt = `
  !n i.
  i IN range n <=> i < n
`;;

let range_set_lt = `
  !n.
  range n = {i | i < n}
`;;

let range_0 = `
  range 0 = {}
`;;

let range_add_1_delete_refl = `
  !n.
  range(n+1) DELETE n = range n
`;;

let finite_range = `
  !n.
  FINITE(range n)
`;;

let card_range = `
  !n.
  CARD(range n) = n
`;;

let swap_permutes_range = `
  !n i j.
  i < n ==>
  j < n ==>
  swap(i,j) permutes range n
`;;

(* maybe use ITSET? *)
let finite_ordering = `
  !S:X->bool.
  FINITE S ==>
  ?f. IMAGE f (range(CARD S)) = S
`;;

(* XXX: relies on CARD S always being finite *)
let injective_finite_ordering = `
  !S:X->bool f.
  IMAGE f (range(CARD S)) = S ==>
  (!x y. x < CARD S ==> y < CARD S ==> f x = f y ==> x = y)
`;;

(* XXX: relies on CARD S always being finite *)
let bij_finite_ordering = `
  !S:X->bool f.
  IMAGE f (range(CARD S)) = S ==>
  BIJ f (range(CARD S)) S
`;;

let image_numseg_antidiagonal = `
  !d:num.
  IMAGE (\a:num. a,d-a) (0..d)
  = {a,b | a + b = d}
`;;

let numseg_le_lt_reflect = `
  !m n:num.
  m <= n ==>
  IMAGE (\a. n - a) {i | i < n - m} = {i | m < i /\ i <= n}
`;;

let numseg_le_reflect_0 = `
  !n:num.
  IMAGE (\a. n - a) (0..n) = (0..n)
`;;

(* ===== reals *)

let real_of_num_plus_minus_minus = `
  !a b.
  &(a+b) - &a - &b = &0:real
`;;

let fact_binom_lemma_37_real = `
  !n i.
  i < n ==>
  &(FACT(n-i) * binom(n,i))
  -
  &(FACT(n-1-i) * binom(n-1,i))
  -
  &((n-1) * FACT(n-1-i) * binom(n-1,i))
  = &0:real
`;;

(* ===== integer sums *)

let isum_integer_sum = `
  !(f:X->int) S.
  FINITE S ==>
  isum S f =
  ring_sum integer_ring S f
`;;

let sum_real_of_int = `
  !(f:X->int) S.
  FINITE S ==>
  sum S (\s. real_of_int (f s))
  = real_of_int (isum S f)
`;;

let int_of_num_sum = `
  !(f:X->num) S.
  FINITE S ==>
  &(nsum S f):int = isum S (\x. &(f x))
`;;

(* ===== rings *)

let ring_div_refl = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  ring_div r c c =
  if ring_unit r c then ring_1 r else ring_0 r
`;;

let ring_add_sub_cancel = `
  !(r:R ring) a b.
  a IN ring_carrier r ==>
  b IN ring_carrier r ==>
  ring_add r a (ring_sub r b a) = b
`;;

let ring_sum_image_injective = `
  !r (f:K->L) (g:L->A) s.
  (!x y. f x = f y ==> x = y)
  ==> ring_sum r (IMAGE f s) g = ring_sum r s (g o f)
`;;

let ring_sum_image_injective_pair = `
  !r (f:A#B->L) (g:L->X) s.
  (!(a,b) (c,d). f (a,b) = f (c,d) ==> (a,b) = (c,d))
  ==> ring_sum r (IMAGE f s) g = ring_sum r s (g o f)
`;;

let ring_sum_delete2 = `
  !(r:R ring) S (f:X->R) s.
  FINITE S ==>
  s IN S ==>
  f s IN ring_carrier r ==>
  ring_sum r S f
  = ring_add r (f s) (ring_sum r (S DELETE s) f)
`;;

let ring_sum_shift1 = `
  !(r:R ring) f n.
  f 0 = ring_0 r ==>
  ring_sum r (0..n+1) f
  = ring_sum r (0..n) (\a. f (a+1))
`;;

let ring_sum_insert_top = `
  !(r:R ring) f n.
  f (n+1) = ring_0 r ==>
  ring_sum r (0..n+1) f
  = ring_sum r (0..n) f
`;;

let ring_mul_sum_mul_delete = `
  !(r:R ring) S:X->bool f:X->R g:X->R x.
  ~(x IN S) ==>
  FINITE S ==>
  g x IN ring_carrier r ==>
  (!s. s IN S ==> g s IN ring_carrier r) ==>
  (!s. s IN S ==> f s IN ring_carrier r) ==>
  ring_mul r
    (g x)
    (ring_sum r S (\s. ring_mul r (f s) (ring_product r (S DELETE s) g)))
  =  ring_sum r S (\s. ring_mul r (f s) (ring_product r ((x INSERT S) DELETE s) g))
`;;

(* simpler special case of RING_SUM_REFLECT *)
let ring_sum_numseg_le_reflect = `
  !(r:R ring) n f:num->R.
  ring_sum r (0..n) f
  = ring_sum r (0..n) (\b. f(n - b))
`;;

let ring_sum_numseg_le_offset = `
  !(r:R ring) m n f:num->R.
  ring_sum r (0..m) f
  = ring_sum r (0..m+n) (\b. if n <= b then f(b - n) else ring_0 r)
`;;

let ring_sum_numseg_le_expand = `
  !(r:R ring) m n f:num->R.
  m <= n ==>
  ring_sum r (0..m) f
  = ring_sum r (0..n) (\a. if a <= m then f(a) else ring_0 r)
`;;

let num_in_subring = `
  !(r:R ring) s.
  s subring_of r ==>
  !n. ring_of_num r n IN s
`;;

let int_in_subring = `
  !(r:R ring) s.
  s subring_of r ==>
  !i. ring_of_int r i IN s
`;;

let ring_sum_subring_generated = `
  !(r:R ring) S A (f:X->R).
  S subring_of r /\
  (!x. x IN A ==> f x IN S) ==>
  ring_sum (subring_generated r S) A f
  = ring_sum r A f
`;;

let ring_sum_subring_generated_v2 = `
  !(r:R ring) S A (f:X->R).
  (!x. x IN A ==> f x IN ring_carrier(subring_generated r S)) ==>
  ring_sum (subring_generated r S) A f
  = ring_sum r A f
`;;

let ring_sum_in_subring = `
  !(r:R ring) G S (f:X->R).
  (!s. s IN S ==> f s IN ring_carrier(subring_generated r G)) ==>
  ring_sum r S f IN ring_carrier(subring_generated r G)
`;;

let ring_product_subring_generated = `
  !(r:R ring) S A (f:X->R).
  S subring_of r /\
  (!x. x IN A ==> f x IN S) ==>
  ring_product (subring_generated r S) A f
  = ring_product r A f
`;;

let ring_product_subring_generated_v2 = `
  !(r:R ring) S A (f:X->R).
  (!x. x IN A ==> f x IN ring_carrier(subring_generated r S)) ==>
  ring_product (subring_generated r S) A f
  = ring_product r A f
`;;

let ring_product_in_subring = `
  !(r:R ring) G S (f:X->R).
  (!s. s IN S ==> f s IN ring_carrier(subring_generated r G)) ==>
  ring_product r S f IN ring_carrier(subring_generated r G)
`;;

let ring_pow_in_subring = `
  !(r:R ring) G f n.
  f IN ring_carrier(subring_generated r G) ==>
  ring_pow r f n IN ring_carrier(subring_generated r G)
`;;

let ring_sum_1 = `
  !(r:R ring) S.
  FINITE S ==>
  ring_sum r S (\s:X. ring_1 r)
  = ring_of_num r (CARD S)
`;;

let ring_sum_num = `
  !(r:R ring) (f:X->num) S.
  FINITE S ==>
  ring_sum r S (\s. ring_of_num r (f s))
  = ring_of_num r (nsum S f)
`;;

let ring_pow_sub1 = `
  !(r:R ring) c d.
  c IN ring_carrier r ==>
  ~(d = 0) ==>
  ring_mul r c (ring_pow r c (d-1)) = ring_pow r c d
`;;

let ring_pow_product = `
  !(r:R ring) (p:X->R) n S.
  FINITE S ==>
  (!s. s IN S ==> p s IN ring_carrier r) ==>
  ring_pow r (ring_product r S p) n
  = ring_product r S (\s:X. ring_pow r (p s) n)
`;;

let ring_sum_numseg_0_diff = `
  !(r:R ring) m n f.
  m <= n ==>
  ring_sum r {i | m < i /\ i <= n} f
  = ring_sub r
      (ring_sum r (0..n) f)
      (ring_sum r (0..m) f)
`;;

let ring_sum_numseg_0_diff_reflect = `
  !(r:R ring) m n f.
  m <= n ==>
  ring_sum r {i | i < n-m} (\i. f(n-i))
  = ring_sub r
      (ring_sum r (0..n) f)
      (ring_sum r (0..m) f)
`;;

let ring_pow_is_product = `
  !(r:R ring) a n.
  a IN ring_carrier r ==>
  ring_pow r a n
  = ring_product r (1..n) (\i. a)
`;;

let ring_sum_sub = `
  !(r:R ring) f g S.
  FINITE S ==>
  (!s:X. s IN S ==> f s IN ring_carrier r) ==>
  (!s:X. s IN S ==> g s IN ring_carrier r) ==>
  ring_sum r S (\s. ring_sub r (f s) (g s))
  = ring_sub r (ring_sum r S f) (ring_sum r S g)
`;;

(* XXX: merge this into ring_ord_unique *)
let unique_prime_valuation_lemma = `
  !(r:R ring) p d e f g.
  integral_domain r ==>
  ring_prime r p ==>
  f IN ring_carrier r ==>
  g IN ring_carrier r ==>
  ~(ring_divides r p g) ==>
  ring_mul r (ring_pow r p d) f
  = ring_mul r (ring_pow r p e) g ==>
  d <= e
`;;

(* XXX: merge this into ring_ord_unique *)
let unique_prime_valuation = `
  !(r:R ring) p d e f g.
  integral_domain r ==>
  ring_prime r p ==>
  f IN ring_carrier r ==>
  g IN ring_carrier r ==>
  ~(ring_divides r p f) ==>
  ~(ring_divides r p g) ==>
  ring_mul r (ring_pow r p d) f
  = ring_mul r (ring_pow r p e) g ==>
  (d = e /\ f = g)
`;;

let ring_sum_const = `
  !(r:R ring) c S.
  FINITE S ==>
  c IN ring_carrier r ==>
  ring_sum r S (\s:X. c)
  = ring_mul r (ring_of_num r (CARD S)) c
`;;

let ring_product_const = `
  !(r:R ring) c S.
  FINITE S ==>
  c IN ring_carrier r ==>
  ring_product r S (\s:X. c) = ring_pow r c (CARD S)
`;;

let ring_of_num_injective_lemma = `
  !(r:R ring) m n.
  ring_char r = 0 ==>
  ring_of_num r m = ring_of_num r n ==>
  n <= m
`;;

(* compare RING_CHAR_EQ_0, RING_OF_NUM_EQ *)
let ring_of_num_injective = `
  !(r:R ring) m n.
  ring_char r = 0 ==>
  ring_of_num r m = ring_of_num r n ==>
  m = n
`;;

let ring_of_num_nonzero = `
  !(r:R ring) n.
  ring_char r = 0 ==>
  ring_of_num r n = ring_0 r ==>
  n = 0
`;;

let neg_ring_of_num_nonzero = `
  !(r:R ring) n.
  ring_char r = 0 ==>
  ring_neg r (ring_of_num r n) = ring_0 r ==>
  n = 0
`;;

let ring_pow_neg_1_mul_refl = `
  !(r:R ring) n.
  ring_mul r (
    ring_pow r (ring_neg r (ring_1 r)) n
  ) (
    ring_pow r (ring_neg r (ring_1 r)) n
  ) = ring_1 r
`;;

let ring_pow_neg_1_plus1 = `
  !(r:R ring) n.
  ring_pow r (ring_neg r (ring_1 r)) (n + 1)
  = ring_neg r (ring_pow r (ring_neg r (ring_1 r)) n)
`;;

let ring_sum_cross_mul = `
  !(r:R ring) P Q (f:X->R) (g:Y->R).
  FINITE P ==>
  FINITE Q ==>
  (!x:X. x IN P ==> f x IN ring_carrier r) ==>
  (!y:Y. y IN Q ==> g y IN ring_carrier r) ==>
  ring_sum r (P CROSS Q) (\(x,y). ring_mul r (f x) (g y))
  = ring_mul r (ring_sum r P f) (ring_sum r Q g)
`;;

let ring_product_1_plus_expand = `
  !(r:R ring) c S.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  ring_product r S (\s:X. ring_add r (ring_1 r) (c s))
  = ring_sum r {A | A SUBSET S} (\A. ring_product r A c)
`;;

let ring_product_sum_expand = `
  !(r:R ring) f Q P.
  FINITE P ==>
  FINITE Q ==>
  (!p q. p IN P ==> q IN Q ==> f p q IN ring_carrier r) ==>
  ring_product r P (\p:X. ring_sum r Q (\q:Y. f p q))
  = ring_sum r
      (functions P Q)
      (\g. ring_product r P (\p. f p (g p)))
`;;

let sub_in_subring = `
  !(r:R ring) G a b.
  a IN ring_carrier r ==>
  b IN ring_carrier(subring_generated r G) ==>
  ( ring_sub r a b IN ring_carrier(subring_generated r G) <=>
    a IN ring_carrier(subring_generated r G)
  )
`;;

let ring_sum_eq_name_d = `
  !(r:R ring) f g S:X->bool.
  (!d. d IN S ==> f d = g d) ==>
  ring_sum r S f = ring_sum r S g
`;;

let ring_product_delete = `
  !(r:R ring) S t f:X->R.
  FINITE S ==>
  t IN S ==>
  f t IN ring_carrier r ==>
  ring_product r S f = ring_mul r (f t) (ring_product r (S DELETE t) f)
`;;

let ring_divides_pow_pow = `
  !(r:R ring) a e f.
  e <= f ==>
  a IN ring_carrier r ==>
  ring_divides r (ring_pow r a e) (ring_pow r a f)
`;;

let ring_product_collect = `
  !(r:R ring) S f:X->R.
  FINITE S ==>
  (!s:X. s IN S ==> f s IN ring_carrier r) ==>
  ring_product r S f =
  ring_product r (IMAGE f S)
    (\y. ring_pow r y (CARD {s | s IN S /\ f s = y}))
`;;

let ring_coprime_1 = `
  !(r:R ring) a.
  a IN ring_carrier r ==>
  (ring_coprime r (ring_1 r,a)
   /\ ring_coprime r (a,ring_1 r)
  )
`;;

let ring_coprime_product_waterfall = `
  !(r:R ring) f:X->R a.
  (UFD r \/ integral_domain r /\ bezout_ring r) ==>
  a IN ring_carrier r ==>
  !S.
  FINITE S ==>
  (!s. s IN S ==> ring_coprime r (a,f s)) ==>
  ring_coprime r (a,ring_product r S f)
`;;

let ring_coprime_product = `
  !(r:R ring) f:X->R a S.
  (UFD r \/ integral_domain r /\ bezout_ring r) ==>
  a IN ring_carrier r ==>
  FINITE S ==>
  (!s. s IN S ==> ring_coprime r (a,f s)) ==>
  ring_coprime r (a,ring_product r S f)
`;;

let ring_product_divides_if_coprime_waterfall = `
  !(r:R ring) f:X->R a.
  (UFD r \/ integral_domain r /\ bezout_ring r) ==>
  a IN ring_carrier r ==>
  !S.
  FINITE S ==>
  (!s t. s IN S ==> t IN S ==> ~(s = t) ==> ring_coprime r (f s,f t)) ==>
  (!s. s IN S ==> ring_divides r (f s) a) ==>
  ring_divides r (ring_product r S f) a
`;;

(* compare product_coprime_primes_divides below *)
let ring_product_divides_if_coprime = `
  !(r:R ring) f:X->R a S.
  (UFD r \/ integral_domain r /\ bezout_ring r) ==>
  a IN ring_carrier r ==>
  FINITE S ==>
  (!s. s IN S ==> ring_divides r (f s) a) ==>
  (!s t. s IN S ==> t IN S ==> ~(s = t) ==> ring_coprime r (f s,f t)) ==>
  ring_divides r (ring_product r S f) a
`;;

let ring_coprime_lpow = `
  !(r:R ring) a b n.
  (UFD r \/ integral_domain r /\ bezout_ring r) ==>
  ring_coprime r (a,b) ==>
  ring_coprime r ((ring_pow r a n),b)
`;;

let ring_coprime_rpow = `
  !(r:R ring) a b n.
  (UFD r \/ integral_domain r /\ bezout_ring r) ==>
  ring_coprime r (a,b) ==>
  ring_coprime r (a,(ring_pow r b n))
`;;

let ring_coprime_lrpow = `
  !(r:R ring) a b m n.
  (UFD r \/ integral_domain r /\ bezout_ring r) ==>
  ring_coprime r (a,b) ==>
  ring_coprime r ((ring_pow r a m),(ring_pow r b n))
`;;

let ring_coprime_associates_prime = `
  !(r:R ring) p q.
  integral_domain r ==>
  ring_prime r p ==>
  ring_prime r q ==>
  (
    ring_coprime r (p,q)
    <=> ~ring_associates r p q
  )
`;;

let ring_divides_associates_prime = `
  !(r:R ring) p q.
  integral_domain r ==>
  ring_prime r p ==>
  ring_prime r q ==>
  (
    ring_divides r p q
    <=> ring_associates r p q
  )
`;;

let ring_divides_product = `
  !(r:R ring) S t:X f.
  FINITE S ==>
  t IN S ==>
  f t IN ring_carrier r ==>
  ring_divides r (f t) (ring_product r S f)
`;;

let ring_sum_restrict_subset = `
  !(r:R ring) S:X->bool U p.
  S SUBSET U ==>
  ring_sum r U (\s. if s IN S then p s else ring_0 r)
  = ring_sum r S p
`;;

let ring_sum_range_add_1 = `
  !(r:R ring) n c:num->R.
  c n IN ring_carrier r ==>
  ring_sum r (range(n+1)) c
  = ring_add r (c n) (ring_sum r (range n) c)
`;;

let ring_sum_range_add_1_sub = `
  !(r:R ring) n c:num->R.
  c n IN ring_carrier r ==>
  ring_sum r (range n) c
  = ring_sub r (ring_sum r (range(n+1)) c) (c n)
`;;

let ring_exp_sum = `
  !(a:A ring) (b:B ring) E:A->B f:X->A S:X->bool.
  FINITE S ==>
  (!x:A. x IN ring_carrier a ==>
         E x IN ring_carrier b) ==>
  E(ring_0 a) = ring_1 b ==>
  (!x y. E(ring_add a x y)
         = ring_mul b (E x) (E y)) ==>
  (!x. x IN S ==> f x IN ring_carrier a) ==>
  E(ring_sum a S f)
  = ring_product b S (E o f)
`;;

(* ===== ring_hasQ: contains copy of Q *)

let ring_hasQ = new_definition `
  ring_hasQ (r:R ring)
  <=> (
    ring_char r = 0 /\
    (!n. ~(n = 0) ==> ring_unit r (ring_of_num r n))
  )
`;;

let ring_hasQ_neg = `
  !(r:R ring) n.
  ring_hasQ r ==>
  ~(n = 0) ==>
  ring_unit r (ring_neg r (ring_of_num r n))
`;;

(* ===== numpreimages *)
(* XXX: inherits weirdness of CARD in infinite case *)

let numpreimages = new_definition `
  numpreimages (f:X->Y) (S:X->bool) y
  = CARD {x | x IN S /\ f x = y}
`;;

let image_numpreimages = `
  !S:X->bool f:X->Y.
  FINITE S ==>
  IMAGE f S
  = {y | ~(numpreimages f S y = 0)}
`;;

(* warmup for numpreimages_permutes_o_perm *)
let numpreimages_o_permutes = `
  !S:X->bool f:X->Y g:X->X.
  FINITE S ==>
  g permutes S ==>
  numpreimages (f o g) S = numpreimages f S
`;;

let numpreimages_permutes_o_perm = `
  !A:X->bool f:X->X g:(X->X)->Y.
  FINITE A ==>
  f permutes A ==>
  numpreimages (\i:X->X. g(f o i)) (perm A)
  = numpreimages g (perm A)
`;;

let ring_sum_fiber_o = `
  !(r:R ring) S:X->bool f:X->Y g:Y->R y.
  FINITE {x | x IN S /\ f x = y} ==>
  g y IN ring_carrier r ==>
  ring_sum r {x | x IN S /\ f x = y} (g o f)
  = ring_mul r (ring_of_num r (numpreimages f S y)) (g y)
`;;

let ring_product_fiber_o = `
  !(r:R ring) S:X->bool f:X->Y g:Y->R y.
  FINITE {x | x IN S /\ f x = y} ==>
  g y IN ring_carrier r ==>
  ring_product r {x | x IN S /\ f x = y} (g o f)
  = ring_pow r (g y) (numpreimages f S y)
`;;

let ring_sum_o = `
  !(r:R ring) S:X->bool f:X->Y g:Y->R.
  FINITE S ==>
  (!y. y IN IMAGE f S ==> g y IN ring_carrier r) ==>
  ring_sum r S (g o f)
  = ring_sum r
      (IMAGE f S)
      (\y. ring_mul r (ring_of_num r (numpreimages f S y)) (g y))
`;;

let ring_sum_o_v2 = `
  !(r:R ring) S:X->bool f:X->Y g:Y->R.
  FINITE S ==>
  (!y. y IN IMAGE f S ==> g y IN ring_carrier r) ==>
  ring_sum r S (g o f)
  = ring_sum r
      {y | ~(numpreimages f S y = 0)}
      (\y. ring_mul r (ring_of_num r (numpreimages f S y)) (g y))
`;;

let ring_sum_o_v3 = `
  !(r:R ring) S:X->bool f:X->Y U:Y->bool g:Y->R.
  FINITE S ==>
  (!y. y IN U ==> g y IN ring_carrier r) ==>
  IMAGE f S SUBSET U ==>
  ring_sum r S (g o f)
  = ring_sum r U
      (\y. ring_mul r (ring_of_num r (numpreimages f S y)) (g y))
`;;

let ring_product_o = `
  !(r:R ring) S:X->bool f:X->Y g:Y->R.
  FINITE S ==>
  (!y. y IN IMAGE f S ==> g y IN ring_carrier r) ==>
  ring_product r S (g o f)
  = ring_product r
      (IMAGE f S)
      (\y. ring_pow r (g y) (numpreimages f S y))
`;;

let ring_product_o_v2 = `
  !(r:R ring) S:X->bool f:X->Y g:Y->R.
  FINITE S ==>
  (!y. y IN IMAGE f S ==> g y IN ring_carrier r) ==>
  ring_product r S (g o f)
  = ring_product r
      {y | ~(numpreimages f S y = 0)}
      (\y. ring_pow r (g y) (numpreimages f S y))
`;;

(* ===== squarefree elements of rings *)

(* XXX: maybe should include a IN ring_carrier r *)
(* XXX: maybe should exclude 0, or exclude non-injective *)
let ring_squarefree = new_definition `
  ring_squarefree(r:R ring) a
  <=>
  (!b. b IN ring_carrier r ==>
   ring_divides r a (ring_mul r b b) ==>
   ring_divides r a b
  )
`;;

let not_squarefree_if_divisible_by_square = `
  !(r:R ring) a b.
  integral_domain r ==>
  ~(a = ring_0 r) ==>
  b IN ring_carrier r ==>
  ~(ring_unit r b) ==>
  ring_divides r (ring_mul r b b) a ==>
  ~(ring_squarefree r a)
`;;

let product_coprime_primes_divides_waterfall = `
  !(r:R ring).
  !P.
  FINITE P ==>
  P SUBSET ring_carrier r ==>
  !b.
  b IN ring_carrier r ==>
  (!p. p IN P ==> ring_prime r p) ==>
  (!p q. p IN P ==> q IN P ==> ring_divides r p q ==> p = q) ==>
  (!p. p IN P ==> ring_divides r p b) ==>
  ring_divides r (ring_product r P I) b
`;;

let product_coprime_primes_divides = `
  !(r:R ring) P b.
  P SUBSET ring_carrier r ==>
  FINITE P ==>
  b IN ring_carrier r ==>
  (!p. p IN P ==> ring_prime r p) ==>
  (!p q. p IN P ==> q IN P ==> ring_divides r p q ==> p = q) ==>
  (!p. p IN P ==> ring_divides r p b) ==>
  ring_divides r (ring_product r P I) b
`;;

let ring_squarefree_if_product_coprime_primes = `
  !(r:R ring) P.
  P SUBSET ring_carrier r ==>
  FINITE P ==>
  (!p. p IN P ==> ring_prime r p) ==>
  (!p q. p IN P ==> q IN P ==> ring_divides r p q ==> p = q) ==>
  ring_squarefree r (ring_product r P I)
`;;

let ring_squarefree_if_product_coprime_primes_indexed = `
  !(r:R ring) S (f:X->R).
  FINITE S ==>
  (!s:X. s IN S ==> f s IN ring_carrier r) ==>
  (!s:X. s IN S ==> ring_prime r (f s)) ==>
  (!s t. s IN S ==> t IN S ==> ring_divides r (f s) (f t) ==> s = t) ==>
  ring_squarefree r (ring_product r S f)
`;;

let ring_squarefree_if_unit = `
  !(r:R ring) p.
  ring_unit r p ==> ring_squarefree r p
`;;

let ring_squarefree_if_prime = `
  !(r:R ring) p.
  ring_prime r p ==> ring_squarefree r p
`;;

let ring_coprime_if_unit = `
  !(r:R ring) a b.
  ring_unit r a ==>
  b IN ring_carrier r ==>
  (ring_coprime r (a,b) /\ ring_coprime r (b,a))
`;;

let ring_product_divides_factor_by_factor = `
  !(r:R ring) (f:X->R) (g:X->R) S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_divides r (f s) (g s)) ==>
  ring_divides r (ring_product r S f) (ring_product r S g)
`;;

let ring_sum_delta_delta = `
  !(r:R ring) S t u a b.
  FINITE S ==>
  t IN S ==>
  u IN S ==>
  a IN ring_carrier r ==>
  b IN ring_carrier r ==>
  ring_sum r S (\s:X. if s = t then a else if s = u then b else ring_0 r) =
  if t = u then a else ring_add r a b
`;;

let ring_product_delta_delta = `
  !(r:R ring) S t u a b.
  FINITE S ==>
  t IN S ==>
  u IN S ==>
  a IN ring_carrier r ==>
  b IN ring_carrier r ==>
  ring_product r S (\s:X. if s = t then a else if s = u then b else ring_1 r) =
  if t = u then a else ring_mul r a b
`;;

let square_divides_product_if_factor_divides_factor = `
  !(r:R ring) S (f:X->R) t u.
  FINITE S ==>
  (!s:X. s IN S ==> f s IN ring_carrier r) ==>
  ~(t = u) ==>
  t IN S ==>
  u IN S ==>
  ring_divides r (f t) (f u) ==>
  ring_divides r
    (ring_mul r (f t) (f t))
    (ring_product r S f)
`;;

let prime_divides_prime_and = `
  !(r:R ring) p q a.
  UFD r ==>
  ring_prime r p ==>
  ring_prime r q ==>
  ring_divides r p q ==>
  ring_divides r p a ==>
  ring_divides r q a
`;;

let ring_squarefree_associates = `
  !(r:R ring) f g.
  ring_associates r f g ==>
  ring_squarefree r f ==>
  ring_squarefree r g
`;;

(* ===== power series and polynomials *)

let poly_neg_subring = `
  !(r:R ring) S (p:(V->num)->R).
  poly_neg (subring_generated r S) p
  = poly_neg r p
`;;

let poly_add_subring = `
  !(r:R ring) S (p:(V->num)->R) q.
  poly_add (subring_generated r S) p q
  = poly_add r p q
`;;

let poly_mul_subring = `
  !(r:R ring) S (p:(V->num)->R) q.
  ring_powerseries (subring_generated r S) p ==>
  ring_powerseries (subring_generated r S) q ==>
  poly_mul (subring_generated r S) p q
  = poly_mul r p q
`;;

let poly_sub_subring = `
  !(r:R ring) S (p:(V->num)->R) q.
  poly_sub (subring_generated r S) p q
  = poly_sub r p q
`;;

let poly_deg_subring = `
  !(r:R ring) G (p:(V->num)->R).
  poly_deg (subring_generated r G) p
  = poly_deg r p
`;;

let poly_evaluate_subring = `
  !(r:R ring) S (p:(V->num)->R) z.
  S subring_of r ==>
  ring_powerseries (subring_generated r S) p ==>
  (!v:V. z v IN S) ==>
  poly_evaluate r p z
  = poly_evaluate (subring_generated r S) p z
`;;

let poly_eval_subring = `
  !(r:R ring) S p z.
  S subring_of r ==>
  ring_powerseries (subring_generated r S) p ==>
  z IN S ==>
  poly_eval r p z
  = poly_eval (subring_generated r S) p z
`;;

let ring_powerseries_subring = `
  !(r:R ring) G (p:(V->num)->R).
  ring_powerseries(subring_generated r G) p ==>
  ring_powerseries r p
`;;

let ring_polynomial_if_subring = `
  !(r:R ring) (p:(V->num)->R).
  ring_polynomial(subring_generated r G) p ==>
  ring_polynomial r p
`;;

let deg_zero_ring = `
  !(r:R ring) (p:(V->num)->R).
  ring_1 r = ring_0 r ==>
  ring_powerseries r p ==>
  poly_deg r p = 0
`;;

let poly_const_subring = `
  !(r:R ring) S c.
  poly_const (subring_generated r S) c
  = poly_const r c:(V->num)->R
`;;

let poly_0_subring = `
  !(r:R ring) S.
  poly_0 (subring_generated r S)
  = poly_0 r:(V->num)->R
`;;

let poly_1_subring = `
  !(r:R ring) S.
  poly_1 (subring_generated r S)
  = poly_1 r:(V->num)->R
`;;

let POWSER_MUL_0 = `(!r (p:(V->num)->A).
        ring_powerseries r p ==> poly_mul r p (poly_0 r) = poly_0 r) /\
   (!r (q:(V->num)->A).
        ring_powerseries r q ==> poly_mul r (poly_0 r) q = poly_0 r)`;;

let powser_ring_carrier = `
  !r:R ring. !s:V->bool.
  ring_carrier(powser_ring r s) = {p | ring_powerseries r p /\ poly_vars r p SUBSET s}
`;;

let poly_ring_carrier = `
  !r:R ring. !s:V->bool.
  ring_carrier(poly_ring r s) = {p | ring_polynomial r p /\ poly_vars r p SUBSET s}
`;;

let poly_in_full_ring = `
  !(r:R ring) p:(V->num)->R.
  ring_polynomial r p
  <=> p IN ring_carrier(poly_ring r (:V))
`;;

let series_in_full_ring = `
  !(r:R ring) p:(V->num)->R.
  ring_powerseries r p
  <=> p IN ring_carrier(powser_ring r (:V))
`;;

let poly_sub_ldistrib_lemma = `
  !(r:R ring) p1 p2 p3.
  p1 IN ring_carrier r ==>
  p2 IN ring_carrier r ==>
  p3 IN ring_carrier r ==>
  ring_mul r p1 (ring_add r p2 (ring_neg r p3)) =
  ring_add r (ring_mul r p1 p2) (ring_neg r (ring_mul r p1 p3))
`;;

let poly_sub_ldistrib = `!r p1 p2 (p3:(V->num)->R).
      ring_powerseries r p1 ==>
      ring_powerseries r p2 ==>
      ring_powerseries r p3
      ==> poly_mul r p1 (poly_sub r p2 p3) =
          poly_sub r (poly_mul r p1 p2) (poly_mul r p1 p3)`;;

let poly_sub_rdistrib_lemma = `
  !(r:R ring) p1 p2 p3.
  p1 IN ring_carrier r ==>
  p2 IN ring_carrier r ==>
  p3 IN ring_carrier r ==>
  ring_mul r (ring_add r p2 (ring_neg r p3)) p1 =
  ring_add r (ring_mul r p2 p1) (ring_neg r (ring_mul r p3 p1))
`;;

let poly_sub_rdistrib = `!r p1 p2 (p3:(V->num)->R).
      ring_powerseries r p1 ==>
      ring_powerseries r p2 ==>
      ring_powerseries r p3
      ==> poly_mul r (poly_sub r p2 p3) p1 =
          poly_sub r (poly_mul r p2 p1) (poly_mul r p3 p1)`;;

let poly_sub_0 = `
  !(r:R ring) p:(V->num)->R.
  ring_powerseries r p ==>
  poly_sub r p (poly_0 r) = p
`;;

let poly_0_sub = `
  !(r:R ring) p:(V->num)->R.
  ring_powerseries r p ==>
  poly_sub r (poly_0 r) p = poly_neg r p
`;;

let poly_vars_empty = `
  !(r:R ring) p:(V->num)->R.
  poly_vars r p = {} <=>
  p = poly_const r (p monomial_1)
`;;

let poly_neg_in_poly_ring = `
  !(r:R ring) p:(V->num)->R S.
  p IN ring_carrier(poly_ring r S) ==>
  poly_neg r p IN ring_carrier(poly_ring r S)
`;;

let poly_add_in_poly_ring = `
  !(r:R ring) p:(V->num)->R q S.
  p IN ring_carrier(poly_ring r S) ==>
  q IN ring_carrier(poly_ring r S) ==>
  poly_add r p q IN ring_carrier(poly_ring r S)
`;;

let poly_sub_in_poly_ring = `
  !(r:R ring) p:(V->num)->R q S.
  p IN ring_carrier(poly_ring r S) ==>
  q IN ring_carrier(poly_ring r S) ==>
  poly_sub r p q IN ring_carrier(poly_ring r S)
`;;

let poly_mul_in_poly_ring = `
  !(r:R ring) p:(V->num)->R q S.
  p IN ring_carrier(poly_ring r S) ==>
  q IN ring_carrier(poly_ring r S) ==>
  poly_mul r p q IN ring_carrier(poly_ring r S)
`;;

let poly_var_o_permutes = `
  !(r:R ring) v:V S f:V->V m.
  f permutes S ==>
  poly_var r v (m o f)
  = poly_var r (f v) m
`;;

let poly_neg_o_permutes = `
  !(r:R ring) p:(V->num)->R (f:V->W) m.
  poly_neg r p (m o f) =
  poly_neg r (\m. p (m o f)) m
`;;

let poly_add_o_permutes = `
  !(r:R ring) p:(V->num)->R q (f:V->W) m.
  poly_add r p q (m o f) =
  poly_add r (\m. p (m o f)) (\m. q (m o f)) m
`;;

let poly_sub_o_permutes = `
  !(r:R ring) p:(V->num)->R q (f:V->W) m.
  poly_sub r p q (m o f) =
  poly_sub r (\m. p (m o f)) (\m. q (m o f)) m
`;;

let poly_mul_o_permutes = `
  !(r:R ring) p:(V->num)->R q S f m.
  f permutes S ==>
  poly_mul r p q (m o f) =
  poly_mul r (\m. p (m o f)) (\m. q (m o f)) m
`;;

let monomial_1_o_permutes = `
  !f S.
  f permutes S ==>
  monomial_1 o f = monomial_1:V->num
`;;

let monomial_1_o_permutes_eq = `
  !m:V->num f S.
  f permutes S ==>
  ( m o f = monomial_1 <=> m = monomial_1 )
`;;

let poly_const_o_permutes = `
  !(r:R ring) c (f:V->V) S.
  f permutes S ==>
  poly_const r c (m o f) = poly_const r c m
`;;

let poly_0_o_permutes = `
  !(r:R ring) (f:V->V) S.
  f permutes S ==>
  poly_0 r (m o f) = poly_0 r m
`;;

let poly_1_o_permutes = `
  !(r:R ring) (f:V->V) S.
  f permutes S ==>
  poly_1 r (m o f) = poly_1 r m
`;;

let finite_monomial_vars_permutes_lemma = `
  !m:V->num f:V->V S.
  f permutes S ==>
  FINITE(monomial_vars m) ==>
  FINITE(monomial_vars (m o f))
`;;

let finite_monomial_vars_permutes = `
  !m:V->num f:V->V S.
  f permutes S ==>
  (
    FINITE(monomial_vars m) <=>
    FINITE(monomial_vars (m o f))
  )
`;;

let infinite_monomial_vars_permutes = `
  !m:V->num f:V->V S.
  f permutes S ==>
  INFINITE(monomial_vars m) ==>
  INFINITE(monomial_vars (m o f))
`;;

let powerseries_o_permutes = `
  !(r:R ring) p (f:V->V) S.
  f permutes S ==>
  ring_powerseries r p ==>
  ring_powerseries r (\m. p (m o f))
`;;

let polynomial_o_permutes = `
  !(r:R ring) p (f:V->V) S.
  f permutes S ==>
  ring_polynomial r p ==>
  ring_polynomial r (\m. p (m o f))
`;;

let poly_var_subring = `
  !(r:R ring) G v:V.
  poly_var(subring_generated r G) v
  = poly_var r v
`;;

let poly_vars_subring = `
  !(r:R ring) G p:(V->num)->R.
  poly_vars(subring_generated r G) p
  = poly_vars r p
`;;

let ring_powerseries_if_polynomial = `
  !(r:R ring) p:(V->num)->R.
  ring_polynomial r p ==>
  ring_powerseries r p
`;;

let ring_polynomial_subring_var = `
  !(r:R ring) G v:V.
  ring_polynomial(subring_generated r G) (poly_var r v)
`;;

let ring_sum_poly_o_permutes = `
  !(r:R ring) p:X->(V->num)->R m f U S.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  f permutes U ==>
  ring_sum(poly_ring r (:V)) S p (m o f) =
  (ring_sum(poly_ring r (:V)) S (\s m. p s (m o f))) m
`;;

let ring_product_poly_o_permutes_waterfall = `
  !(r:R ring) p:X->(V->num)->R f U S.
  FINITE S ==>
  !m.
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  f permutes U ==>
  ring_product(poly_ring r (:V)) S p (m o f) =
  (ring_product(poly_ring r (:V)) S (\s m. p s (m o f))) m
`;;

let ring_product_poly_o_permutes = `
  !(r:R ring) p:X->(V->num)->R m f U S.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  f permutes U ==>
  ring_product(poly_ring r (:V)) S p (m o f) =
  (ring_product(poly_ring r (:V)) S (\s m. p s (m o f))) m
`;;

(* ===== x_series(r) = the ring r[[x]] *)
(* ===== x_poly(r) = the ring r[x] *)

let x_series = new_definition `
  x_series (r:R ring) =
  powser_ring r (:1)
`;;

let x_poly = new_definition `
  x_poly (r:R ring) =
  poly_ring r (:1)
`;;

(* XXX: factor more definitions through this *)
let series_from_coeffs = new_definition `
  series_from_coeffs (f:num->R)
  = (\m. f(m one))
`;;

let x_poly_vars_1 = `
  !r:R ring.
  !p:(1->num)->R.
  poly_vars r p SUBSET (:1)
`;;

let x_series_carrier = `
  !r:R ring.
  ring_carrier(x_series r) = {p | ring_powerseries r p}
`;;

(* XXX: merge with x_series_use, generalize everything *)
let powser_use = `
  !(r:R ring).
  poly_0 r = ring_0(powser_ring r (:V))
  /\ poly_1 r = ring_1(powser_ring r (:V))
  /\ poly_neg r = ring_neg(powser_ring r (:V))
  /\ poly_add r = ring_add(powser_ring r (:V))
  /\ poly_mul r = ring_mul(powser_ring r (:V))
  /\ !p. ring_powerseries r p <=> p IN ring_carrier(powser_ring r (:V))
`;;

let x_series_use = `
  !(r:R ring).
  poly_0 r = ring_0(x_series r)
  /\ poly_1 r = ring_1(x_series r)
  /\ poly_neg r = ring_neg(x_series r)
  /\ poly_add r = ring_add(x_series r)
  /\ poly_mul r = ring_mul(x_series r)
  /\ !p. ring_powerseries r p <=> p IN ring_carrier(x_series r)
`;;

let x_poly_carrier = `
  !r:R ring.
  ring_carrier(x_poly r) = {p | ring_polynomial r p}
`;;

(* XXX: merge with x_poly_use, generalize everything *)
let poly_use = `
  !(r:R ring).
  poly_0 r = ring_0(poly_ring r (:V))
  /\ poly_1 r = ring_1(poly_ring r (:V))
  /\ poly_neg r = ring_neg(poly_ring r (:V))
  /\ poly_add r = ring_add(poly_ring r (:V))
  /\ poly_mul r = ring_mul(poly_ring r (:V))
  /\ !p. ring_polynomial r p <=> p IN ring_carrier(poly_ring r (:V))
`;;

let x_poly_use = `
  !(r:R ring).
  poly_0 r = ring_0(x_poly r)
  /\ poly_1 r = ring_1(x_poly r)
  /\ poly_neg r = ring_neg(x_poly r)
  /\ poly_add r = ring_add(x_poly r)
  /\ poly_mul r = ring_mul(x_poly r)
  /\ !p. ring_polynomial r p <=> p IN ring_carrier(x_poly r)
`;;

let x_series_sub_use = `
  !(r:R ring).
  poly_sub r = ring_sub(x_series r)
`;;

let x_poly_sub_use = `
  !(r:R ring).
  poly_sub r = ring_sub(x_poly r)
`;;

let x_poly_carrier_in_series_carrier = `
  !r:R ring.
  !p.
  p IN ring_carrier(x_poly r)
  ==> p IN ring_carrier(x_series r)
`;;

let x_poly_carrier_subset_series_carrier = `
  !r:R ring.
  ring_carrier(x_poly r) SUBSET ring_carrier(x_series r)
`;;

let x_poly_subring_in_poly_carrier = `
  !(r:R ring) G p.
  p IN ring_carrier(x_poly(subring_generated r G)) ==>
  p IN ring_carrier(x_poly r)
`;;

let ring_of_num_x_series = `
  !(r:R ring) n.
  ring_of_num(x_series r) n
  = poly_const r (ring_of_num r n)
`;;

let ring_char_x_series = `
  !(r:R ring).
  ring_char (x_series r) = ring_char r
`;;

(* ===== x_monomial *)

let x_monomial = new_definition `
  x_monomial (d:num) = \v:1. d
`;;

let x_monomial_deg = `
  !d. monomial_deg(x_monomial d) = d
`;;

let x_monomial_0_monomial_1 = `
  x_monomial 0 = monomial_1
`;;

let x_monomial_add = `
  !a b.
  monomial_mul (x_monomial a) (x_monomial b) = x_monomial (a+b)
`;;

let x_monomial_surjective = `
  !m. ?d. x_monomial d = m
`;;

let x_monomial_injective = `
  !d e.
  x_monomial d = x_monomial e ==>
  d = e
`;;

let ring_sum_image_x_monomial = `
  !(r:R ring) (g:(1->num)->R) s.
  ring_sum r (IMAGE x_monomial s) g = ring_sum r s (g o x_monomial)
`;;

let x_series_monomial_mul_finite = `
  !m:1->num.
  FINITE {(m1,m2) | monomial_mul m1 m2 = m}
`;;

let x_monomial_pair_injective = `
  !(a,b) (c,d).
  (\(a,b). x_monomial a,x_monomial b) (a,b) = (\(a,b). x_monomial a,x_monomial b) (c,d) ==>
  (a,b) = (c,d)
`;;

let ring_sum_image_x_monomial_pair = `
  !(r:R ring) (g:(1->num)#(1->num)->R) (s:num#num->bool).
  ring_sum r (IMAGE (\(a,b). x_monomial a,x_monomial b) s) g
  = ring_sum r s (g o (\(a,b). x_monomial a,x_monomial b))
`;;

let x_monomial_factorizations = `
  !d (m:1->num) (n:1->num).
  monomial_mul m n = x_monomial d ==>
  ?a b. a + b = d /\ m = x_monomial a /\ n = x_monomial b
`;;

let x_monomial_factorizations_set = `
  !d.
  {m,n:1->num | monomial_mul m n = x_monomial d}
  = IMAGE (\(a,b). x_monomial a,x_monomial b) {a,b | a+b = d}
`;;

(* ===== coeff d p = coefficient of x^d in p *)

let coeff = new_definition `
  coeff (d:num) (p:(1->num)->R)
  = p(x_monomial d)
`;;

let eq_coeff = `
  !(r:R ring) (p:(1->num)->R) q.
  (!d. coeff d p = coeff d q)
  ==> p = q
`;;

let coeff_series_in_ring = `
  !(r:R ring) p.
  ring_powerseries r p <=>
  !d. coeff d p IN ring_carrier(r)
`;;

let coeff_series_from_coeffs = `
  !(r:R ring) (f:num->R) d.
  coeff d (series_from_coeffs f) = f d
`;;

let series_from_coeffs_coeff = `
  !(r:R ring) f:(1->num)->R.
  series_from_coeffs (\d. coeff d f) = f
`;;

let series_series_from_coeffs = `
  !(r:R ring) (f:num->R).
  ring_powerseries r (series_from_coeffs f)
  <=> (!d. f d IN ring_carrier r)
`;;

let poly_series_from_coeffs = `
  !(r:R ring) (f:num->R).
  ring_polynomial r (series_from_coeffs f)
  <=> ((!d. f d IN ring_carrier r)
       /\ FINITE {d | ~(f d = ring_0 r)}
      )
`;;

let poly_coeff = `
  !(r:R ring) p:(1->num)->R.
  ring_polynomial r p
  <=> ((!d. coeff d p IN ring_carrier r)
       /\ FINITE {d | ~(coeff d p = ring_0 r)}
      )
`;;

let ring_polynomial_subring_if_coeffs = `
  !(r:R ring) (p:(1->num)->R).
  ring_polynomial r p ==>
  (!d. coeff d p IN ring_carrier(subring_generated r G)) ==>
  ring_polynomial(subring_generated r G) p
`;;

let coeff_series_carrier_in_ring = `
  !(r:R ring) p.
  p IN ring_carrier(x_series r) <=>
  !d. coeff d p IN ring_carrier(r)
`;;

let coeff_poly_in_ring = `
  !(r:R ring) d p.
  ring_polynomial r p ==>
  coeff d p IN ring_carrier(r)
`;;

let coeff_poly_carrier_in_ring = `
  !(r:R ring) d p.
  p IN ring_carrier(x_poly r) ==>
  coeff d p IN ring_carrier(r)
`;;

let coeff_poly_const = `
  !(r:R ring) c:R d.
  coeff d (poly_const r c)
  = if d = 0 then c else ring_0 r
`;;

let coeff_poly_0 = `
  !(r:R ring).
  coeff d (poly_0 r)
  = ring_0 r
`;;

let coeff_poly_1 = `
  !(r:R ring).
  coeff d (poly_1 r)
  = if d = 0 then ring_1 r else ring_0 r
`;;

let coeff_poly_neg = `
  !(r:R ring) p d.
  coeff d (poly_neg r p)
  = ring_neg r (coeff d p)
`;;

let coeff_poly_add = `
  !(r:R ring) p q d.
  coeff d (poly_add r p q)
  = ring_add r (coeff d p) (coeff d q)
`;;

let coeff_series_add = `
  !(r:R ring) p q d.
  coeff d (ring_add(x_series r) p q)
  = ring_add r (coeff d p) (coeff d q)
`;;

let coeff_poly_sub = `
  !(r:R ring) p q d.
  coeff d (poly_sub r p q)
  = ring_sub r (coeff d p) (coeff d q)
`;;

let coeff_poly_mul_lemma = `
  !(r:R ring) p q.
  ((\(m1,m2). ring_mul r (p m1) (q m2)) o (\(a,b). x_monomial a,x_monomial b)) =
  (\(a,b). ring_mul r (p (x_monomial a)) (q (x_monomial b)))
`;;

let coeff_poly_mul = `
  !(r:R ring) p q d.
  coeff d (poly_mul r p q)
  = ring_sum r {a,b | a+b = d} (\(a,b). ring_mul r (coeff a p) (coeff b q))
`;;

let coeff_poly_mul_oneindex = `
  !(r:R ring) d p q.
  coeff d (poly_mul r p q)
  = ring_sum(r) (0..d) (\a. ring_mul r (coeff a p) (coeff (d-a) q))
`;;

(* XXX: use this to prove coeff_poly_const_times *)
let poly_const_times = `
  !(r:R ring) c:R p:(V->num)->R.
  c IN ring_carrier r ==>
  ring_powerseries r p ==>
  poly_mul r (poly_const r c) p
  = (\m. ring_mul r c (p m))
`;;

let coeff_poly_const_times = `
  !(r:R ring) c:R p d.
  c IN ring_carrier r ==>
  ring_powerseries r p ==>
  coeff d (poly_mul r (poly_const r c) p)
  = ring_mul r c (coeff d p)
`;;

let coeff_times_poly_const = `
  !(r:R ring) c:R p d.
  c IN ring_carrier r ==>
  ring_powerseries r p ==>
  coeff d (poly_mul r p (poly_const r c))
  = ring_mul r c (coeff d p)
`;;

let polynomial_if_coeff = `
  !(r:R ring) p n.
  ring_powerseries r p ==>
  (!d. ~(coeff d p = ring_0 r) ==> d <= n) ==>
  ring_polynomial r p
`;;

let deg_le_coeff = `
  !(r:R ring) p n.
  ring_powerseries r p ==>
  (!d. ~(coeff d p = ring_0 r) ==> d <= n) ==>
  poly_deg r p <= n
`;;

let deg_coeff = `
  !(r:R ring) p n.
  ring_powerseries r p ==>
  (!d. ~(coeff d p = ring_0 r) ==> d <= n) ==>
  ~(coeff n p = ring_0 r) ==>
  poly_deg r p = n
`;;

let topcoeff_nonzero = `
  !(r:R ring) p.
  ring_polynomial r p ==>
  (p = poly_0 r <=> coeff (poly_deg r p) p = ring_0 r)
`;;

let coeff_deg_le = `
  !(r:R ring) p n d.
  ring_polynomial r p ==>
  poly_deg r p <= n ==>
  ~(coeff d p = ring_0 r) ==>
  d <= n
`;;

let coeff_le_deg = `
  !(r:R ring) p d.
  ring_polynomial r p ==>
  ~(coeff d p = ring_0 r) ==>
  d <= poly_deg r p
`;;

let finite_coeff = `
  !(r:R ring) p.
  ring_polynomial r p ==>
  FINITE {d | ~(coeff d p = ring_0 r)}
`;;

let poly_if_coeff = `
  !(r:R ring) p n.
  ring_powerseries r p ==>
  (!d. n <= d ==> coeff d p = ring_0 r) ==>
  ring_polynomial r p
`;;

let deg_coeff_from_le = `
  !(r:R ring) p n.
  ring_polynomial r p ==>
  poly_deg r p <= n ==>
  ~(coeff n p = ring_0 r) ==>
  poly_deg r p = n
`;;

let poly_eval_expand_coeff = `
  !(r:R ring) p x n.
  ring_polynomial r p ==>
  x IN ring_carrier r ==>
  poly_deg r p <= n ==>
  poly_eval r p x
  = ring_sum r (0..n)
      (\d. ring_mul r (coeff d p) (ring_pow r x d))
`;;

let deg_mul_const_le = `
  !(r:R ring) (p:(V->num)->R) c.
  ring_polynomial r p ==>
  c IN ring_carrier r ==>
  poly_deg r (poly_mul r p (poly_const r c))
  <= poly_deg r p
`;;

let deg_const_mul_le = `
  !(r:R ring) (p:(V->num)->R) c.
  ring_polynomial r p ==>
  c IN ring_carrier r ==>
  poly_deg r (poly_mul r (poly_const r c) p)
  <= poly_deg r p
`;;

let poly_mul_const_const = `
  !(r:R ring) (p:(V->num)->R) c d.
  ring_polynomial r p ==>
  c IN ring_carrier r ==>
  d IN ring_carrier r ==>
  poly_mul r (poly_mul r p (poly_const r c)) (poly_const r d)
  = poly_mul r p (poly_const r (ring_mul r c d))
`;;

let poly_mul_const_const_1 = `
  !(r:R ring) (p:(V->num)->R) c d.
  ring_polynomial r p ==>
  c IN ring_carrier r ==>
  d IN ring_carrier r ==>
  ring_mul r c d = ring_1 r ==>
  poly_mul r (poly_mul r p (poly_const r c)) (poly_const r d)
  = p
`;;

let deg_mul_const_const_1 = `
  !(r:R ring) (p:(V->num)->R) c d.
  ring_polynomial r p ==>
  c IN ring_carrier r ==>
  d IN ring_carrier r ==>
  ring_mul r c d = ring_1 r ==>
  poly_deg r (poly_mul r p (poly_const r c))
  = poly_deg r p
`;;

let deg_mul_unit_const = `
  !(r:R ring) (p:(V->num)->R) c.
  ring_polynomial r p ==>
  ring_unit r c ==>
  poly_deg r (poly_mul r p (poly_const r c))
  = poly_deg r p
`;;

let associates_if_mul_unit_const = `
  !(r:R ring) (p:(V->num)->R) c.
  ring_polynomial r p ==>
  ring_unit r c ==>
  ring_associates(poly_ring r (:V)) p (poly_mul r p (poly_const r c))
`;;

(* ===== cx^d *)

let const_x_pow = new_definition `
  const_x_pow (r:R ring) (c:R) (d:num)
  = \m. if m one = d then c else ring_0 r
`;;

let const_x_pow_0 = `
  !(r:R ring) c.
  const_x_pow r c 0 = poly_const r c
`;;

let const_0_x_pow = `
  !(r:R ring) n.
  const_x_pow r (ring_0 r) n = poly_0 r
`;;

let const_x_pow_series = `
  !(r:R ring) c d.
  c IN ring_carrier r ==>
  ring_powerseries r (const_x_pow r c d)
`;;

let const_x_pow_poly_lemma = `
  !(r:R ring) d:num.
  {m:1->num | ~((if m one = d then c else ring_0 r) = ring_0 r)} SUBSET {\v. d}
`;;

let const_x_pow_poly_lemma2 = `
  !(r:R ring) d:num.
  FINITE {m:1->num | ~((if m one = d then c else ring_0 r) = ring_0 r)}
`;;

let const_x_pow_poly = `
  !(r:R ring) c d.
  c IN ring_carrier r ==>
  ring_polynomial r (const_x_pow r c d)
`;;

let coeff_const_x_pow = `
  !(r:R ring) c d e.
  coeff e (const_x_pow r c d)
  = if e = d then c else ring_0 r
`;;

let coeff_const_x_pow_times = `
  !(r:R ring) c d p e.
  c IN ring_carrier r ==>
  ring_powerseries r p ==>
  coeff e (poly_mul r (const_x_pow r c d) p)
  = if e < d then ring_0 r else ring_mul r c (coeff (e - d) p)
`;;

let deg_const_x_pow_le = `
  !(r:R ring) c d.
  c IN ring_carrier r ==>
  poly_deg r (const_x_pow r c d) <= d
`;;

let deg_const_x_pow = `
  !(r:R ring) c d.
  c IN ring_carrier r ==>
  ~(c = ring_0 r) ==>
  poly_deg r (const_x_pow r c d) = d
`;;

let eval_const_x_pow = `
  !(r:R ring) c n x.
  c IN ring_carrier r ==>
  x IN ring_carrier r ==>
  poly_eval r (const_x_pow r c n) x
  = ring_mul r c (ring_pow r x n)
`;;

let subring_const_x_pow = `
  !(r:R ring) S c n.
  const_x_pow (subring_generated r S) c n
  = const_x_pow r c n
`;;

let const_1_x_pow = `
  !(r:R ring).
  const_x_pow r (ring_1 r) 0 = poly_1 r
`;;

(* ===== x^d *)

let x_pow = new_definition `
  x_pow (r:R ring) (d:num)
  = const_x_pow r (ring_1 r) d
`;;

let x_pow_1 = `
  !(r:R ring).
  x_pow r 1 = poly_var r one
`;;

let x_pow_0 = `
  !(r:R ring).
  x_pow r 0 = poly_1 r
`;;

let x_pow_poly = `
  !(r:R ring) d.
  ring_polynomial r (x_pow r d)
`;;

let x_pow_series = `
  !(r:R ring) d.
  ring_powerseries r (x_pow r d)
`;;

let coeff_x_pow = `
  !(r:R ring) d e.
  coeff e (x_pow r d)
  = if e = d then ring_1 r else ring_0 r
`;;

let coeff_x_pow_times = `
  !(r:R ring) d p e.
  ring_powerseries r p ==>
  coeff e (poly_mul r (x_pow r d) p)
  = if e < d then ring_0 r else coeff (e - d) p
`;;

let x_pow_add = `
  !(r:R ring) m n.
  x_pow r (m+n)
  = poly_mul r (x_pow r m) (x_pow r n)
`;;

let deg_x_pow_le = `
  !(r:R ring) d.
  poly_deg r (x_pow r d) <= d
`;;

let deg_x_pow = `
  !(r:R ring) d.
  ~(ring_1 r = ring_0 r) ==>
  poly_deg r (x_pow r d) = d
`;;

let eval_x_pow = `
  !(r:R ring) n x.
  x IN ring_carrier r ==>
  poly_eval r (x_pow r n) x
  = ring_pow r x n
`;;

let subring_x_pow = `
  !(r:R ring) S n.
  x_pow (subring_generated r S) n
  = x_pow r n
`;;

(* ===== x-c *)

let x_minus_const = new_definition `
  x_minus_const (r:R ring) (c:R)
  = poly_sub r (x_pow r 1) (poly_const r c)
`;;

let x_minus_const_poly = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  ring_polynomial r (x_minus_const r c)
`;;

let x_minus_const_series = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  ring_powerseries r (x_minus_const r c)
`;;

let coeff_x_minus_const = `
  !(r:R ring) c e.
  c IN ring_carrier r ==>
  coeff e (x_minus_const r c)
  = if e = 1 then ring_1 r else if e = 0 then ring_neg r c else ring_0 r
`;;

let coeff_x_minus_const_times = `
  !(r:R ring) c p e.
  c IN ring_carrier r ==>
  ring_powerseries r p ==>
  coeff e (poly_mul r (x_minus_const r c) p)
  = if e = 0 then ring_mul r (ring_neg r c) (coeff 0 p)
    else ring_sub r (coeff (e-1) p) (ring_mul r c (coeff e p))
`;;

let x_minus_const_0 = `
  !(r:R ring).
  x_minus_const r (ring_0 r) = x_pow r 1
`;;

let deg_x_minus_const_le = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  poly_deg r (x_minus_const r c) <= 1
`;;

let deg_x_minus_const = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  ~(ring_1 r = ring_0 r) ==>
  poly_deg r (x_minus_const r c) = 1
`;;

let x_minus_const_nonzero = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  ~(ring_1 r = ring_0 r) ==>
  ~(x_minus_const r c = poly_0 r)
`;;

let eval_x_minus_const = `
  !(r:R ring) c x.
  c IN ring_carrier r ==>
  x IN ring_carrier r ==>
  poly_eval r (x_minus_const r c) x
  = ring_sub r x c
`;;

let eval_x_minus_const_refl = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  poly_eval r (x_minus_const r c) c
  = ring_0 r
`;;

let x_minus_const_not_unit = `
  !(r:R ring) z.
  integral_domain r ==>
  z IN ring_carrier r ==>
  ~ring_unit(x_poly r) (x_minus_const r z)
`;;

(* ===== 1-cx *)

let one_minus_constx = new_definition `
  one_minus_constx (r:R ring) (c:R)
  = poly_sub r (x_pow r 0) (const_x_pow r c 1)
`;;

let one_minus_constx_poly = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  ring_polynomial r (one_minus_constx r c)
`;;

let one_minus_constx_series = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  ring_powerseries r (one_minus_constx r c)
`;;

let coeff_one_minus_constx = `
  !(r:R ring) c e.
  c IN ring_carrier r ==>
  coeff e (one_minus_constx r c)
  = if e = 0 then ring_1 r else if e = 1 then ring_neg r c else ring_0 r
`;;

let coeff_one_minus_constx_times = `
  !(r:R ring) c p e.
  c IN ring_carrier r ==>
  ring_powerseries r p ==>
  coeff e (poly_mul r (one_minus_constx r c) p)
  = if e = 0 then coeff 0 p
    else ring_sub r (coeff e p) (ring_mul r c (coeff (e-1) p))
`;;

let deg_one_minus_constx_le = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  poly_deg r (one_minus_constx r c) <= 1
`;;

let eval_one_minus_constx = `
  !(r:R ring) c x.
  c IN ring_carrier r ==>
  x IN ring_carrier r ==>
  poly_eval r (one_minus_constx r c) x
  = ring_sub r (ring_1 r) (ring_mul r c x)
`;;

let nonzero_one_minus_constx = `
  !(r:R ring) c.
  ~(ring_1 r = ring_0 r) ==>
  c IN ring_carrier r ==>
  ~(one_minus_constx r c = poly_0 r)
`;;

(* ===== infinite geometric series *)
(* in r[[x]]; different topology from SUMS_GP etc. *)

(* infinite_geometric_series r c = sum c^n x^n *)
let infinite_geometric_series = new_definition `
  infinite_geometric_series (r:R ring) (c) =
  \n. (ring_pow r c (n one))
`;;

let infinite_geometric_series_powerseries = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  ring_powerseries r (infinite_geometric_series r c)
`;;

(* sum c^n x^n is in r[[x]] *)
let infinite_geometric_series_x_series = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  infinite_geometric_series r c IN ring_carrier(x_series r)
`;;

let coeff_infinite_geometric_series = `
  !(r:R ring) c e.
  coeff e (infinite_geometric_series r c)
  = ring_pow r c e
`;;

(* (1-cx) sum c^n x^n = 1 *)
let infinite_geometric_series_inverse = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  poly_mul r (one_minus_constx r c) (infinite_geometric_series r c)
  = poly_1 r
`;;

(* ===== poly_pow *)

let poly_pow = new_definition `
  poly_pow (r:R ring)
  = ring_pow (powser_ring r (:V))
`;;

let poly_pow_series = `
  !(r:R ring) p:(V->num)->R n.
  ring_powerseries r p ==>
  ring_powerseries r (poly_pow r p n)
`;;

let poly_pow_poly = `
  !(r:R ring) p:(V->num)->R n.
  ring_polynomial r p ==>
  ring_polynomial r (poly_pow r p n)
`;;

let poly_pow_in_poly_ring = `
  !(r:R ring) p:(V->num)->R n S.
  p IN ring_carrier(poly_ring r S) ==>
  poly_pow r p n IN ring_carrier(poly_ring r S)
`;;

let x_series_use_pow = `
  !(r:R ring).
  poly_pow r = ring_pow (x_series r)
`;;

let x_poly_use_pow = `
  !(r:R ring).
  poly_pow r = ring_pow (x_poly r)
`;;

let poly_ring_use_pow = `
  !(r:R ring).
  poly_pow r = ring_pow (poly_ring r (:V))
`;;

let poly_pow_0 = `
  !(r:R ring) p:(V->num)->R.
  poly_pow r p 0 = poly_1 r:(V->num)->R
`;;

let poly_pow_1 = `
  !(r:R ring) p:(V->num)->R.
  ring_powerseries r p ==>
  poly_pow r p 1 = p
`;;

let poly_1_pow = `
  !(r:R ring) n.
  poly_pow r (poly_1 r) n = poly_1 r:(V->num)->R
`;;

let poly_pow_add = `
  !(r:R ring) (p:(V->num)->R) m n.
  ring_powerseries r p ==>
  poly_pow r p (m+n) = poly_mul r (poly_pow r p m) (poly_pow r p n)
`;;

let x_pow_pow = `
  !(r:R ring) m n.
  poly_pow r (x_pow r m) n
  = x_pow r (m*n)
`;;

let poly_pow_mul = `
  !(r:R ring) (p:(V->num)->R) m n.
  ring_powerseries r p ==>
  poly_pow r (poly_pow r p m) n
  = poly_pow r p (m*n)
`;;

let poly_mul_pow = `
  !(r:R ring) (p:(V->num)->R) q n.
  ring_powerseries r p ==>
  ring_powerseries r q ==>
  poly_pow r (poly_mul r p q) n
  = poly_mul r (poly_pow r p n) (poly_pow r q n)
`;;

let poly_deg_pow_le = `
  !(r:R ring) (p:(V->num)->R) n.
  ring_polynomial r p ==>
  poly_deg r (poly_pow r p n) <= n * poly_deg r p
`;;

let coeff_pow_infinite_geometric_series = `
  !(r:R ring) c e n.
  c IN ring_carrier r ==>
  coeff n (poly_pow r (infinite_geometric_series r c) (e+1))
  = ring_mul r
      (ring_of_num r (binom(n+e,e)))
      (ring_pow r c n)
`;;

let pow_infinite_geometric_series = `
  !(r:R ring) c e.
  c IN ring_carrier r ==>
  poly_pow r (infinite_geometric_series r c) (e+1)
  = series_from_coeffs (\n.
      ring_mul r
        (ring_of_num r (binom(n+e,e)))
        (ring_pow r c n))
`;;

let pow_infinite_geometric_series_inverse_lemma = `
  !(r:R ring) c e.
  c IN ring_carrier r ==>
  poly_mul r
    (poly_pow r (one_minus_constx r c) (e+1))
    (poly_pow r (infinite_geometric_series r c) (e+1))
  = poly_1 r
`;;

(* (1-cx)^(e+1) sum binom(n+e,e) c^n x^n = 1 *)
let pow_infinite_geometric_series_inverse = `
  !(r:R ring) c e.
  c IN ring_carrier r ==>
  poly_mul r
    (poly_pow r (one_minus_constx r c) (e+1))
    (series_from_coeffs (\n.
      ring_mul r
        (ring_of_num r (binom(n+e,e)))
        (ring_pow r c n)))
  = poly_1 r
`;;

let poly_pow_o_permutes = `
  !(r:R ring) p:(V->num)->R S f n m.
  f permutes S ==>
  ring_powerseries r p ==>
  poly_pow r p n (m o f) =
  poly_pow r (\m. p (m o f)) n m
`;;

let eval_poly_pow_multi = `
  !(r:R ring) (p:(V->num)->R) c U n.
  p IN ring_carrier(poly_ring r U) ==>
  (!v. v IN U ==> c v IN ring_carrier r) ==>
  poly_evaluate r (poly_pow r p n) c
  = ring_pow r (poly_evaluate r p c) n
`;;

let poly_const_pow = `
  !(r:R ring) c n.
  c IN ring_carrier r ==>
  poly_const r (ring_pow r c n)
  = poly_pow r (poly_const r c) n:(V->num)->R
`;;

(* ===== x_monomial_shift: x^d |-> x^(d+1) *)

let x_monomial_shift = new_definition `
  x_monomial_shift (m:1->num)
  = (\v. m v + 1)
`;;

let x_monomial_shift_eq_x_monomial = `
  !m d.
  x_monomial_shift m = x_monomial d
  <=>
  (?c. d = c + 1 /\ m = x_monomial c)
`;;

let x_monomial_shift_is_not_monomial_1 = `
  !m.
  ~(x_monomial_shift m = monomial_1)
`;;

let x_monomial_shift_mul = `
  !m n.
  monomial_mul (x_monomial_shift m) n
  = x_monomial_shift (monomial_mul m n)
`;;

let x_monomial_mul_shift = `
  !m n.
  monomial_mul m (x_monomial_shift n)
  = x_monomial_shift (monomial_mul m n)
`;;

let x_monomial_shift_injective = `
  !m n.
  x_monomial_shift m = x_monomial_shift n ==>
  m = n
`;;

(* ===== univariate derivatives *)

let x_derivative = new_definition `
  x_derivative (r:R ring) (p:(1->num)->R)
  = (\m. ring_mul r
          (ring_of_num r (m one + 1))
          (p (x_monomial_shift m)))
`;;

let x_derivative_series = `
  !(r:R ring) p.
  ring_powerseries r p ==>
  ring_powerseries r (x_derivative r p)
`;;

let x_derivative_polynomial = `
  !(r:R ring) p.
  ring_polynomial r p ==>
  ring_polynomial r (x_derivative r p)
`;;

let coeff_x_derivative = `
  !(r:R ring) p d.
  coeff d (x_derivative r p)
  = ring_mul r (ring_of_num r (d+1)) (coeff (d+1) p)
`;;

let x_derivative_add_series = `
  !(r:R ring) p q.
  ring_powerseries r p ==>
  ring_powerseries r q ==>
  x_derivative r (poly_add r p q)
  = poly_add r (x_derivative r p) (x_derivative r q)
`;;

let x_derivative_neg_series = `
  !(r:R ring) p.
  ring_powerseries r p ==>
  x_derivative r (poly_neg r p)
  = poly_neg r (x_derivative r p)
`;;

let x_derivative_sub_series = `
  !(r:R ring) p q.
  ring_powerseries r p ==>
  ring_powerseries r q ==>
  x_derivative r (poly_sub r p q)
  = poly_sub r (x_derivative r p) (x_derivative r q)
`;;

let x_derivative_poly_const = `
  !(r:R ring) c.
  x_derivative r (poly_const r c) = poly_0 r
`;;

let x_derivative_poly_0 = `
  !(r:R ring).
  x_derivative r (poly_0 r) = poly_0 r
`;;

let x_derivative_poly_1 = `
  !(r:R ring).
  x_derivative r (poly_1 r) = poly_0 r
`;;

let x_derivative_poly_const_mul_series = `
  !(r:R ring) c p.
  c IN ring_carrier r ==>
  ring_powerseries r p ==>
  x_derivative r (poly_mul r (poly_const r c) p)
  = poly_mul r (poly_const r c) (x_derivative r p)
`;;

let x_derivative_const_x_pow = `
  !(r:R ring) e.
  c IN ring_carrier r ==>
  x_derivative r (const_x_pow r c e)
  = const_x_pow r (ring_mul r (ring_of_num r e) c) (e-1)
`;;

let x_derivative_x_pow = `
  !(r:R ring) e.
  x_derivative r (x_pow r e)
  = const_x_pow r (ring_of_num r e) (e-1)
`;;

let coeff_x_derivative_poly_mul = `
  !(r:R ring) p q d.
  ring_powerseries r p ==>
  ring_powerseries r q ==>
  coeff d (x_derivative r (poly_mul r p q))
  = ring_add r
      (coeff d (poly_mul r (x_derivative r p) q))
      (coeff d (poly_mul r p (x_derivative r q)))
`;;

let x_derivative_mul = `
  !(r:R ring) p q.
  ring_powerseries r p ==>
  ring_powerseries r q ==>
  x_derivative r (poly_mul r p q)
  = poly_add r
      (poly_mul r (x_derivative r p) q)
      (poly_mul r p (x_derivative r q))
`;;

let x_derivative_mul_const = `
  !(r:R ring) c q.
  c IN ring_carrier r ==>
  ring_powerseries r q ==>
  x_derivative r (poly_mul r (poly_const r c) q)
  = poly_mul r (poly_const r c) (x_derivative r q)
`;;

let x_derivative_x_minus_const = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  x_derivative r (x_minus_const r c) = poly_1 r
`;;

let x_derivative_one_minus_constx = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  x_derivative r (one_minus_constx r c) = poly_const r (ring_neg r c)
`;;

let x_derivative_subring = `
  !(r:R ring) G p.
  x_derivative (subring_generated r G) p
  = x_derivative r p
`;;

(* basically: derivative of sp/sq is derivative of p/q *)
let x_derivative_ratio_scaling = `
  !(r:R ring) p q s.
  ring_powerseries r p ==>
  ring_powerseries r q ==>
  ring_powerseries r s ==>
  poly_sub r (
    poly_mul r (
      x_derivative r (poly_mul r s p)
    ) (
      poly_mul r s q
    )
  ) (
    poly_mul r (
      poly_mul r s p
    ) (
      x_derivative r (poly_mul r s q)
    )
  )
  =
  poly_mul r (
    poly_pow r s 2
  ) (
    poly_sub r (
      poly_mul r (x_derivative r p) (q)
    ) (
      poly_mul r (p) (x_derivative r q)
    )
  )
`;;

(* ===== sums of finite sequences of power series *)

let poly_sum = new_definition `
  poly_sum (r:R ring) (S:X->bool) (p:X->(1->num)->R)
  = ring_sum(x_series r) S p
`;;

let poly_sum_empty = `
  !(r:R ring) p:X->(1->num)->R.
  poly_sum r {} p = poly_0 r
`;;

let poly_sum_insert = `
  !(r:R ring) p:X->(1->num)->R S t.
  FINITE S ==>
  poly_sum r (t INSERT S) p =
  (if ring_powerseries r (p t) ==> t IN S
   then poly_sum r S p
   else poly_add r (p t) (poly_sum r S p))
`;;

let poly_sum_delete2 = `
  !(r:R ring) S p:X->(1->num)->R t.
  FINITE S ==>
  t IN S ==>
  ring_powerseries r (p t) ==>
  poly_sum r S p
  = poly_add r (p t) (poly_sum r (S DELETE t) p)
`;;

let poly_sum_series = `
  !(r:R ring) p:X->(1->num)->R S.
  FINITE S ==>
  (!s. s IN S ==> ring_powerseries r (p s)) ==>
  ring_powerseries r (poly_sum r S p)
`;;

(* XXX: merge into poly_sum_series *)
let series_sum_series_multi = `
  !(r:R ring) p:X->(V->num)->R S.
  FINITE S ==>
  (!s. s IN S ==> ring_powerseries r (p s)) ==>
  ring_powerseries r (ring_sum(powser_ring r (:V)) S p)
`;;

let poly_sum_ring_sum_x_poly = `
  !(r:R ring) p:X->(1->num)->R S.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  poly_sum r S p = ring_sum(x_poly r) S p
`;;

let poly_sum_poly = `
  !(r:R ring) p:X->(1->num)->R S.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  ring_polynomial r (poly_sum r S p)
`;;

let poly_sum_eq = `
  !(r:R ring) S:X->bool p:X->(1->num)->R q:X->(1->num)->R.
  (!s. s IN S ==> p s = q s) ==>
  poly_sum r S p = poly_sum r S q
`;;

let coeff_poly_sum = `
  !(r:R ring) p:X->(1->num)->R d:num S:X->bool.
  FINITE S ==>
  (!s. s IN S ==> ring_powerseries r (p s)) ==>
  coeff d (poly_sum r S p) =
  ring_sum r S (\s. coeff d (p s))
`;;

let x_derivative_sum = `
  !(r:R ring) p (S:X->bool).
  FINITE S ==>
  (!s. s IN S ==> ring_powerseries r (p s)) ==>
  x_derivative r (poly_sum r S p)
  = poly_sum r S (\s. x_derivative r (p s))
`;;

let poly_deg_sum_le = `
  !(r:R ring) (p:X->(1->num)->R) n S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial r (p s)) ==>
  (!s:X. s IN S ==> poly_deg r (p s) <= n) ==>
  poly_deg r (poly_sum r S p) <= n
`;;

let poly_sum_lmul = `
  !(r:R ring) (p:X->(1->num)->R) c S.
  ring_powerseries r c ==>
  FINITE S ==>
  (!s:X. s IN S ==> ring_powerseries r (p s)) ==>
  poly_sum r S (\s. poly_mul r c (p s))
  = poly_mul r c (poly_sum r S p)
`;;

let poly_sum_const = `
  !(r:R ring) (p:(1->num)->R) S.
  ring_powerseries r p ==>
  FINITE S ==>
  poly_sum r S (\s:X. p)
  = poly_mul r (poly_const r (ring_of_num r (CARD S))) p
`;;

(* XXX: merge into poly_sum_poly *)
let poly_sum_poly_multi = `
  !(r:R ring) p:X->(V->num)->R S.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  ring_polynomial r (ring_sum(poly_ring r (:V)) S p)
`;;

(* XXX: merge *)
let poly_sum_subring_multi = `
  !(r:R ring) G (p:X->(V->num)->R) S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial(subring_generated r G) (p s)) ==>
  ring_sum(poly_ring(subring_generated r G) (:V)) S p
  = ring_sum(poly_ring r (:V)) S p
`;;

let ring_polynomial_subring_sum = `
  !(r:R ring) G p:X->(V->num)->R S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial(subring_generated r G) (p s)) ==>
  ring_polynomial(subring_generated r G) (ring_sum(poly_ring r (:V)) S p)
`;;

let poly_sum_restrict_subset = `
  !(r:R ring) S:X->bool U p.
  S SUBSET U ==>
  poly_sum r U (\s. if s IN S then p s else poly_0 r)
  = poly_sum r S p
`;;

let poly_const_sum = `
  !(r:R ring) f:X->R S.
  FINITE S ==>
  (!s. s IN S ==> f s IN ring_carrier r) ==>
  poly_const r (ring_sum r S f) =
  poly_sum r S (\s. poly_const r (f s))
`;;

(* ===== products of finite sequences of power series *)

let poly_product = new_definition `
  poly_product (r:R ring) (S:X->bool) (p:X->(1->num)->R)
  = ring_product(x_series r) S p
`;;

let poly_product_empty = `
  !(r:R ring) p:X->(1->num)->R.
  poly_product r {} p = poly_1 r
`;;

let poly_product_insert = `
  !(r:R ring) p:X->(1->num)->R S t.
  FINITE S ==>
  poly_product r (t INSERT S) p =
  (if ring_powerseries r (p t) ==> t IN S
   then poly_product r S p
   else poly_mul r (p t) (poly_product r S p))
`;;

let poly_product_1 = `
  !(r:R ring) S.
  poly_product r S (\s:X. poly_1 r)
  = poly_1 r
`;;

let poly_product_eq = `
  !(r:R ring) p:X->(1->num)->R q S.
  (!s. s IN S ==> p s = q s) ==>
  poly_product r S p = poly_product r S q
`;;

(* XXX: merge into poly_product_series *)
let poly_product_series_multi = `
  !(r:R ring) p:X->(V->num)->R S.
  FINITE S ==>
  (!s. s IN S ==> ring_powerseries r (p s)) ==>
  ring_powerseries r (ring_product(powser_ring r (:V)) S p)
`;;

(* XXX: merge into poly_product_poly *)
let poly_product_poly_multi = `
  !(r:R ring) p:X->(V->num)->R S.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  ring_polynomial r (ring_product(poly_ring r (:V)) S p)
`;;

let poly_product_series = `
  !(r:R ring) p:X->(1->num)->R S.
  FINITE S ==>
  (!s. s IN S ==> ring_powerseries r (p s)) ==>
  ring_powerseries r (poly_product r S p)
`;;

let poly_product_poly = `
  !(r:R ring) p:X->(1->num)->R S.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  ring_polynomial r (poly_product r S p)
`;;

let poly_product_ring_product_x_poly = `
  !(r:R ring) p:X->(1->num)->R S.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  poly_product r S p
  = ring_product(x_poly r) S p
`;;

let poly_product_pow = `
  !(r:R ring) S (p:X->(1->num)->R) n.
  FINITE S ==>
  (!s. s IN S ==> ring_powerseries r (p s)) ==>
  poly_pow r (poly_product r S p) n
  = poly_product r S (\s:X. poly_pow r (p s) n)
`;;

let poly_mul_sum_mul_delete = `
  !(r:R ring) S:X->bool f:X->(1->num)->R g:X->(1->num)->R x.
  ~(x IN S) ==>
  FINITE S ==>
  ring_powerseries r (g x) ==>
  (!s. s IN S ==> ring_powerseries r (g s)) ==>
  (!s. s IN S ==> ring_powerseries r (f s)) ==>
  poly_mul r
    (g x)
    (poly_sum r S (\s. poly_mul r (f s) (poly_product r (S DELETE s) g)))
  =  poly_sum r S (\s. poly_mul r (f s) (poly_product r ((x INSERT S) DELETE s) g))
`;;

let x_derivative_product = `
  !(r:R ring) p (S:X->bool).
  FINITE S ==>
  (!s. s IN S ==> ring_powerseries r (p s)) ==>
  x_derivative r (poly_product r S p)
  = poly_sum r S
      (\s. poly_mul r
             (x_derivative r (p s))
             (poly_product r (S DELETE s) p))
`;;

let poly_product_const = `
  !(r:R ring) (p:(1->num)->R) S.
  ring_powerseries r p ==>
  FINITE S ==>
  poly_product r S (\s:X. p) = poly_pow r p (CARD S)
`;;

let poly_pow_is_product = `
  !(r:R ring) (p:(1->num)->R) n.
  ring_powerseries r p ==>
  poly_pow r p n = poly_product r (1..n) (\i. p)
`;;

let x_derivative_pow = `
  !(r:R ring) p n.
  ring_powerseries r p ==>
  x_derivative r (poly_pow r p n)
  =
  poly_mul r (
    poly_const r (ring_of_num r n)
  ) (
    poly_mul r (
      x_derivative r p
    ) (
      poly_pow r p (n-1)
    )
  )
`;;

let eval_poly_product = `
  !(r:R ring) p:(X->(1->num)->R) z S.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  z IN ring_carrier r ==>
  poly_eval r (poly_product r S p) z
  = ring_product r S (\s. poly_eval r (p s) z)
`;;

(* XXX: merge into poly_product_subring; generalize other poly_product theorems *)
let poly_product_subring_multi = `
  !(r:R ring) G (p:X->(V->num)->R) S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial(subring_generated r G) (p s)) ==>
  ring_product(poly_ring(subring_generated r G) (:V)) S p
  = ring_product(poly_ring r (:V)) S p
`;;

let poly_product_subring = `
  !(r:R ring) G (p:X->(1->num)->R) S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_powerseries(subring_generated r G) (p s)) ==>
  poly_product (subring_generated r G) S p
  = poly_product r S p
`;;

let ring_polynomial_subring_product = `
  !(r:R ring) G p:X->(V->num)->R S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial(subring_generated r G) (p s)) ==>
  ring_polynomial(subring_generated r G) (ring_product(poly_ring r (:V)) S p)
`;;

let poly_product_image = `
  !(r:R ring) S (f:X->Y) (g:Y->(1->num)->R).
  (!x y. x IN S ==> y IN S ==> f x = f y ==> x = y) ==>
  poly_product r (IMAGE f S) g = poly_product r S (g o f)
`;;

let poly_deg_product_le = `
  !(r:R ring) (p:X->(1->num)->R) n S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial r (p s)) ==>
  (!s:X. s IN S ==> poly_deg r (p s) <= n s) ==>
  poly_deg r (poly_product r S p) <= nsum S n
`;;

(* should factor via poly_deg_product_le *)
let poly_deg_product_each_le = `
  !(r:R ring) (p:X->(1->num)->R) n S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial r (p s)) ==>
  (!s:X. s IN S ==> poly_deg r (p s) <= n) ==>
  poly_deg r (poly_product r S p) <= (CARD S) * n
`;;

let poly_product_delete = `
  !(r:R ring) S t f:X->((1->num)->R).
  FINITE S ==>
  t IN S ==>
  ring_powerseries r (f t) ==>
  poly_product r S f = poly_mul r (f t) (poly_product r (S DELETE t) f)
`;;

let poly_pow_subring = `
  !(r:R ring) G (p:(V->num)->R) n.
  ring_powerseries(subring_generated r G) p ==>
  poly_pow (subring_generated r G) p n
  = poly_pow r p n
`;;

let poly_product_botcoeff1 = `
  !(r:R ring) (p:X->(1->num)->R) S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial r (p s)) ==>
  (!s:X. s IN S ==> coeff 0 (p s) = ring_1 r) ==>
  coeff 0 (poly_product r S p) = ring_1 r
`;;

let poly_product_in_poly_ring = `
  !(r:R ring) (p:X->(V->num)->R) E S.
  FINITE S ==>
  (!s:X. s IN S ==> p s IN ring_carrier(poly_ring r E)) ==>
  ring_product(poly_ring r (:V)) S p IN ring_carrier(poly_ring r E)
`;;

let powser_product_o_permutes = `
  !(r:R ring) p:X->(V->num)->R U f S.
  FINITE S ==>
  !m.
  f permutes U ==>
  (!s. s IN S ==> ring_powerseries r (p s)) ==>
  ring_product(powser_ring r (:V)) S p (m o f) =
  ring_product(powser_ring r (:V)) S (\s m. (p s) (m o f)) m
`;;

let poly_product_o_permutes = `
  !(r:R ring) p:X->(V->num)->R U f S.
  FINITE S ==>
  !m.
  f permutes U ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  ring_product(poly_ring r (:V)) S p (m o f) =
  ring_product(poly_ring r (:V)) S (\s m. (p s) (m o f)) m
`;;

(* XXX: merge into eval_poly_product *)
let eval_poly_product_multi = `
  !(r:R ring) (p:X->(V->num)->R) c U S.
  FINITE S ==>
  (!s:X. s IN S ==> p s IN ring_carrier(poly_ring r U)) ==>
  (!v. v IN U ==> c v IN ring_carrier r) ==>
  poly_evaluate r (ring_product(poly_ring r (:V)) S p) c
  = ring_product r S (\s. poly_evaluate r (p s) c)
`;;

let poly_product_restrict_subset = `
  !(r:R ring) S:X->bool U p.
  S SUBSET U ==>
  poly_product r U (\s. if s IN S then p s else poly_1 r)
  = poly_product r S p
`;;

let poly_const_product = `
  !(r:R ring) f:X->R S.
  FINITE S ==>
  (!t. t IN S ==> f t IN ring_carrier r) ==>
  poly_const r (ring_product r S f) =
  poly_product r S (\t. poly_const r (f t))
`;;

(* ===== monic_vanishing_at: prod_i (x-c_i) *)

let monic_vanishing_at = new_definition `
  monic_vanishing_at (r:R ring) (S:X->bool) (c:X->R)
  = poly_product r S (\s. x_minus_const r (c s))
`;;

let monic_vanishing_at_empty = `
  !(r:R ring) c:X->R.
  monic_vanishing_at r {} c = poly_1 r
`;;

let monic_vanishing_at_insert = `
  !(r:R ring) S:X->bool c t.
  (c t) IN ring_carrier r ==>
  FINITE S ==>
  monic_vanishing_at r (t INSERT S) c
  = if t IN S
    then monic_vanishing_at r S c
    else poly_mul r (x_minus_const r (c t)) (monic_vanishing_at r S c)
`;;

let monic_vanishing_at_plus1 = `
  !(r:R ring) c n.
  (c n) IN ring_carrier r ==>
  monic_vanishing_at r {i:num | i < n+1} c
  = poly_mul r (x_minus_const r (c n)) (monic_vanishing_at r {i:num | i < n} c)
`;;

let monic_vanishing_at_eq = `
  !(r:R ring) S:X->bool c d.
  (!s:X. s IN S ==> c s = d s) ==>
  monic_vanishing_at r S c = monic_vanishing_at r S d
`;;

let monic_vanishing_at_poly = `
  !(r:R ring) S c:X->R.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  ring_polynomial r (monic_vanishing_at r S c)
`;;

let monic_vanishing_at_series = `
  !(r:R ring) S c:X->R.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  ring_powerseries r (monic_vanishing_at r S c)
`;;

let x_derivative_monic_vanishing_at = `
  !(r:R ring) S c:X->R.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  x_derivative r (monic_vanishing_at r S c)
  = poly_sum r S
      (\s. (monic_vanishing_at r (S DELETE s) c))
`;;

let eval_monic_vanishing_at = `
  !(r:R ring) S (c:X->R) z.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  z IN ring_carrier r ==>
  poly_eval r (monic_vanishing_at r S c) z
  = ring_product r S (\s. ring_sub r z (c s))
`;;

(* compare INTEGRAL_DOMAIN_PRODUCT_EQ_0 *)
let ring_product_eq_0 = `
  !(r:R ring) S (f:X->R).
  FINITE S /\
  (!s. s IN S ==> f s IN ring_carrier r) /\
  (?t. t IN S /\ f t = ring_0 r) ==>
  ring_product r S f = ring_0 r
`;;

let eval_monic_vanishing_at_refl = `
  !(r:R ring) S (c:X->R) t.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  t IN S ==>
  poly_eval r (monic_vanishing_at r S c) (c t)
  = ring_0 r
`;;

let monic_vanishing_at_image = `
  !(r:R ring) S (f:X->Y) (g:Y->R).
  (!x y. x IN S ==> y IN S ==> f x = f y ==> x = y) ==>
  monic_vanishing_at r (IMAGE f S) g = monic_vanishing_at r S (g o f)
`;;

(* ===== monic polynomials *)

let monic = new_definition `
  monic (r:R ring) (p:(1->num)->R)
  <=> coeff (poly_deg r p) p = ring_1 r
`;;

let monic_zero_ring = `
  !(r:R ring) p.
  ring_1 r = ring_0 r ==>
  ring_powerseries r p ==>
  monic r p
`;;

let monic_poly_0 = `
  !(r:R ring).
  monic r (poly_0 r) <=> ring_1 r = ring_0 r
`;;

let monic_poly_1 = `
  !(r:R ring).
  monic r (poly_1 r)
`;;

let poly_1_if_monic_deg_0 = `
  !(r:R ring) p.
  ring_polynomial r p ==>
  poly_deg r p = 0 ==>
  monic r p ==>
  p = poly_1 r
`;;

let monic_x_pow = `
  !(r:R ring) n.
  monic r (x_pow r n)
`;;

let monic_x_minus_const = `
  !(r:R ring) c.
  c IN ring_carrier r ==>
  monic r (x_minus_const r c)
`;;

let topcoeff_monic_poly_mul = `
  !(r:R ring) p q.
  ring_polynomial r p ==>
  ring_polynomial r q ==>
  monic r p ==>
  monic r q ==>
  coeff (poly_deg r p + poly_deg r q) (poly_mul r p q)
  = ring_1 r
`;;

let deg_monic_poly_mul = `
  !(r:R ring) p q.
  ring_polynomial r p ==>
  ring_polynomial r q ==>
  monic r p ==>
  monic r q ==>
  poly_deg r (poly_mul r p q) = poly_deg r p + poly_deg r q
`;;

let monic_poly_mul = `
  !(r:R ring) p q.
  ring_polynomial r p ==>
  ring_polynomial r q ==>
  monic r p ==>
  monic r q ==>
  monic r (poly_mul r p q)
`;;

let monic_poly_product = `
  !(r:R ring) p (S:X->bool).
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  (!s. s IN S ==> monic r (p s)) ==>
  monic r (poly_product r S p)
`;;

let monic_vanishing_at_monic = `
  !(r:R ring) S:X->bool c.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  monic r (monic_vanishing_at r S c)
`;;

let monic_subring = `
  !(r:R ring) G p.
  monic (subring_generated r G) p
  <=> monic r p
`;;

(* ===== r[x] when r is a field *)

let PID_x_poly_field = `
  !r:R ring.
  field r ==> PID(x_poly r)
`;;

let UFD_x_poly_field = `
  !r:R ring.
  field r ==> UFD(x_poly r)
`;;

let integral_domain_x_poly_field = `
  !r:R ring.
  field r ==> integral_domain(x_poly r)
`;;

let prime_iff_irreducible_over_field = `
  !(r:R ring) p.
  field r ==>
  (ring_irreducible(x_poly r) p <=> ring_prime(x_poly r) p)
`;;

let squarefree_if_irreducible_over_field = `
  !(r:R ring) p.
  field r ==>
  ring_irreducible(x_poly r) p ==>
  ring_squarefree(x_poly r) p
`;;

let x_poly_field_monic_associate = `
  !(r:R ring) (p:(1->num)->R).
  field r ==>
  ring_polynomial r p ==>
  ~(p = poly_0 r) ==>
  ?q. (ring_polynomial r q /\
       monic r q /\
       ring_associates(x_poly r) p q)
`;;

let mul_unit_const_if_associates = `
  !(r:R ring) (p:(V->num)->R) q.
  field r ==>
  ring_associates(poly_ring r (:V)) p q ==>
  ?c. ring_unit r c /\ q = poly_mul r p (poly_const r c)
`;;

let monic_associates = `
  !(r:R ring) p q.
  field r ==>
  monic r p ==>
  monic r q ==>
  ring_associates(x_poly r) p q ==>
  p = q
`;;

let no_square_divisor_if_coprime_derivative_lemma1 = `
  !(r:R ring) q (u:(V->num)->R).
  ring_polynomial r q ==>
  ring_polynomial r u ==>
  poly_mul r (poly_mul r q q) u
  = poly_mul r q (poly_mul r q u)
`;;

let no_square_divisor_if_coprime_derivative_lemma2 = `
  !(r:R ring) q u.
  ring_polynomial r q ==>
  ring_polynomial r u ==>
     poly_add r
     (poly_mul r
      (poly_add r (poly_mul r (x_derivative r q) q)
      (poly_mul r q (x_derivative r q)))
     u)
     (poly_mul r (poly_mul r q q) (x_derivative r u)) =
     poly_mul r q
     (poly_add r
      (poly_mul r (poly_add r (x_derivative r q) (x_derivative r q)) u)
     (poly_mul r q (x_derivative r u)))
`;;

let no_square_divisor_if_coprime_derivative = `
  !(r:R ring) p q.
  field r ==>
  ring_polynomial r q ==>
  ring_coprime(x_poly r) (p,x_derivative r p) ==>
  ring_divides(x_poly r) (poly_mul r q q) p ==>
  ring_unit(x_poly r) q
`;;

let nonzero_if_coprime_derivative = `
  !(r:R ring) p.
  field r ==>
  ring_coprime(x_poly r) (p,x_derivative r p) ==>
  ~(p = poly_0 r)
`;;

let squarefree_if_coprime_derivative = `
  !(r:R ring) p.
  field r ==>
  ring_coprime(x_poly r) (p,x_derivative r p) ==>
  ring_squarefree(x_poly r) p
`;;

let deg_x_derivative_lemma = `
  !(r:R ring) p d.
  ring_polynomial r p ==>
  ~(coeff d (x_derivative r p) = ring_0(r:R ring)) ==>
  d <= poly_deg r p - 1
`;;

let deg_x_derivative_le = `
  !(r:R ring) p.
  ring_polynomial r p ==>
  poly_deg r (x_derivative r p) <= poly_deg r p - 1
`;;

(* warning: 0 - 1 = 0 *)
let deg_x_derivative = `
  !(r:R ring) p.
  integral_domain r ==>
  ring_char r = 0 ==>
  ring_polynomial r p ==>
  poly_deg r (x_derivative r p) = poly_deg r p - 1
`;;

let x_derivative_nonzero = `
  !(r:R ring) p.
  integral_domain r ==>
  ring_char r = 0 ==>
  ring_polynomial r p ==>
  ~(poly_deg r p = 0) ==>
  ~(x_derivative r p = poly_0 r)
`;;

let deg_divides = `
  !(r:R ring) (S:V->bool) p q.
  integral_domain r ==>
  ring_divides(poly_ring r S) p q ==>
  ~(q = poly_0 r) ==>
  poly_deg r p <= poly_deg r q
`;;

let poly_deg_product = `
  !(r:R ring) p n S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial r (p s)) ==>
  (!s:X. s IN S ==> ~(p s = poly_0 r)) ==>
  (!s:X. s IN S ==> poly_deg r (p s) = n s) ==>
  field r ==>
  poly_deg r (poly_product r S p) = nsum S n
`;;

let deg_prime = `
  !(r:R ring) p.
  field r ==>
  ring_prime(x_poly r) p ==>
  ~(poly_deg r p = 0)
`;;

let deg_0_if_unit = `
  !(r:R ring) p.
  field r ==>
  ring_unit(x_poly r) p ==>
  poly_deg r p = 0
`;;

let prime_if_deg_1 = `
  !(r:R ring) p.
  field r ==>
  ring_polynomial r p ==>
  poly_deg r p = 1 ==>
  ring_prime(x_poly r) p
`;;

let coprime_prime_derivative = `
  !(r:R ring) p.
  field r ==>
  ring_char r = 0 ==>
  ring_prime(x_poly r) p ==>
  ring_coprime(x_poly r) (p,x_derivative r p)
`;;

let square_divides_if_also_divides_derivative = `
  !(r:R ring) p f.
  field r ==>
  ring_char r = 0 ==>
  ring_prime(x_poly r) p ==>
  ring_divides(x_poly r) p f ==>
  ring_divides(x_poly r) p (x_derivative r f) ==>
  ring_divides(x_poly r) (poly_mul r p p) f
`;;

let poly_divides_product = `
  !(r:R ring) p (f:X->(1->num)->R) S t.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial r (f s)) ==>
  t IN S ==>
  ring_divides(x_poly r) p (f t) ==>
  ring_divides(x_poly r) p (poly_product r S f)
`;;

let poly_divides_sum = `
  !(r:R ring) p (f:X->(1->num)->R) S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_divides(x_poly r) p (f s)) ==>
  ring_polynomial r p ==>
  ring_divides(x_poly r) p (poly_sum r S f)
`;;

let poly_divides_delta = `
  !(r:R ring) p t (f:X->(1->num)->R) S.
  FINITE S ==>
  t IN S ==>
  ring_polynomial r (f t) ==>
  (!s:X. s IN S ==> ~(s = t) ==> ring_divides(x_poly r) p (f s)) ==>
  ring_divides(x_poly r) p (poly_sum r S f) ==>
  ring_divides(x_poly r) p (f t)
`;;

let coprime_product = `
  !(r:R ring) p (f:X->R) S.
  FINITE S ==>
  (UFD r \/ (integral_domain r /\ bezout_ring r)) ==>
  p IN ring_carrier r ==>
  (!s:X. s IN S ==> ring_coprime r (p,f s)) ==>
  ring_coprime r (p,ring_product r S f)
`;;

let divides_factor_and_derivative_product = `
  !(r:R ring) S t p (f:X->(1->num)->R).
  field r ==>
  FINITE S ==>
  t IN S ==>
  ring_divides(x_poly r) p (f t) ==>
  (!s:X. s IN S DELETE t ==> ring_coprime(x_poly r) (p,f s)) ==>
  ring_divides(x_poly r) p (x_derivative r (poly_product r S f)) ==>
  ring_divides(x_poly r) p (x_derivative r (f t))
`;;

let coprime_derivative_if_squarefree = `
  !(r:R ring) f.
  field r ==>
  ring_char r = 0 ==>
  ring_polynomial r f ==>
  ~(f = poly_0 r) ==>
  ring_squarefree(x_poly r) f ==>
  ring_coprime(x_poly r) (f,x_derivative r f)
`;;

let gcd_poly_linear_combination = `
  !(r:R ring) a b.
  field r ==>
  ring_polynomial r a ==>
  ring_polynomial r b ==>
  ?x y.
    ring_polynomial r x /\
    ring_polynomial r y /\
    poly_add r (poly_mul r a x) (poly_mul r b y)
      = ring_gcd(x_poly r) (a,b)
`;;

let linear_combination_if_coprime_poly = `
  !(r:R ring) a b.
  field r ==>
  ring_coprime(x_poly r) (a,b) ==>
  ?x y.
    ring_polynomial r x /\
    ring_polynomial r y /\
    poly_add r (poly_mul r a x) (poly_mul r b y) = poly_1 r
`;;

let coprime_poly_if_linear_combination = `
  !(r:R ring) a b x y.
  ring_polynomial r a ==>
  ring_polynomial r b ==>
  ring_polynomial r x ==>
  ring_polynomial r y ==>
  poly_add r (poly_mul r a x) (poly_mul r b y) = poly_1 r ==>
  ring_coprime(x_poly r) (a,b)
`;;

let nonzero_poly_mul = `
  !(r:R ring) p (q:(1->num)->R).
  integral_domain r ==>
  ring_powerseries r p ==>
  ring_powerseries r q ==>
  ~(p = poly_0 r) ==>
  ~(q = poly_0 r) ==>
  ~(poly_mul r p q = poly_0 r)
`;;

let nonzero_poly_pow = `
  !(r:R ring) (p:(1->num)->R) n.
  integral_domain r ==>
  ring_powerseries r p ==>
  ~(p = poly_0 r) ==>
  ~(poly_pow r p n = poly_0 r)
`;;

let nonzero_poly_product = `
  !(r:R ring) S p.
  integral_domain r ==>
  FINITE S ==>
  (!s:X. s IN S ==> ~(p s = poly_0 r)) ==>
  ~(poly_product r S p = poly_0 r)
`;;

let irred_x_minus_const = `
  !(r:R ring) c.
  field r ==>
  c IN ring_carrier r ==>
  (
    ring_polynomial r (x_minus_const r c) /\
    ring_irreducible (x_poly r) (x_minus_const r c) /\
    monic r (x_minus_const r c)
  )
`;;

let monic_factorization = `
  !(r:R ring) f.
  field r ==>
  ring_polynomial r f ==>
  monic r f ==>
  ?n p. (
    (!i. i IN (1..n) ==> ring_polynomial r (p i)) /\
    (!i. i IN (1..n) ==> monic r (p i)) /\
    (!i. i IN (1..n) ==> ring_irreducible(x_poly r) (p i)) /\
    poly_product r (1..n) p = f
  )
`;;

let monic_factorization_exponents = `
  !(r:R ring) f.
  field r ==>
  ring_polynomial r f ==>
  monic r f ==>
  ?P e. (
    FINITE P /\
    (!p. p IN P ==> ring_polynomial r p) /\
    (!p. p IN P ==> monic r p) /\
    (!p. p IN P ==> ring_irreducible(x_poly r) p) /\
    (!p. p IN P ==> ~(e p = 0)) /\
    poly_product r P (\p. poly_pow r p (e p)) = f
  )
`;;

(* ===== polynomial reversal *)

let x_truncreverse = new_definition `
  x_truncreverse (r:R ring) n (p:(1->num)->R)
  = \m. if m one <= n then p (\v. n - m one) else ring_0 r
`;;

let coeff_x_truncreverse = `
  !(r:R ring) n p d.
  coeff d (x_truncreverse r n p)
  = if d <= n then coeff (n - d) p else ring_0 r
`;;

let x_truncreverse_series = `
  !(r:R ring) n p.
  ring_powerseries r p ==>
  ring_powerseries r (x_truncreverse r n p)
`;;

let x_truncreverse_poly = `
  !(r:R ring) n p.
  ring_powerseries r p ==>
  ring_polynomial r (x_truncreverse r n p)
`;;

let deg_x_truncreverse_le = `
  !(r:R ring) n p.
  ring_powerseries r p ==>
  poly_deg r (x_truncreverse r n p) <= n
`;;

let x_truncreverse_poly_add = `
  !(r:R ring) n p q.
  x_truncreverse r n (poly_add r p q)
  = poly_add r (x_truncreverse r n p) (x_truncreverse r n q)
`;;

let x_truncreverse_poly_sub = `
  !(r:R ring) n p q.
  x_truncreverse r n (poly_sub r p q)
  = poly_sub r (x_truncreverse r n p) (x_truncreverse r n q)
`;;

let x_truncreverse_poly_const = `
  !(r:R ring) n c.
  x_truncreverse r n (poly_const r c)
  = const_x_pow r c n
`;;

let x_truncreverse_0_poly_const = `
  !(r:R ring) c.
  x_truncreverse r 0 (poly_const r c)
  = poly_const r c
`;;

let x_truncreverse_poly_1 = `
  !(r:R ring) n.
  x_truncreverse r n (poly_1 r)
  = x_pow r n
`;;

let x_truncreverse_poly_0 = `
  !(r:R ring) n.
  x_truncreverse r n (poly_0 r)
  = poly_0 r
`;;

let x_truncreverse_poly_sum = `
  !(r:R ring) n p:X->(1->num)->R S:X->bool.
  FINITE S ==>
  (!s. s IN S ==> ring_powerseries r (p s)) ==>
  x_truncreverse r n (poly_sum r S p)
  = poly_sum r S (\s. x_truncreverse r n (p s))
`;;

let x_truncreverse_const_x_pow = `
  !(r:R ring) n c.
  x_truncreverse r n (const_x_pow r c n)
  = poly_const r c
`;;

let x_truncreverse_x_pow = `
  !(r:R ring) n.
  x_truncreverse r n (x_pow r n)
  = poly_1 r
`;;

let x_truncreverse_x_minus_const = `
  !(r:R ring) c.
  x_truncreverse r 1 (x_minus_const r c)
  = one_minus_constx r c
`;;

let x_truncreverse_one_minus_constx = `
  !(r:R ring) c.
  x_truncreverse r 1 (one_minus_constx r c)
  = x_minus_const r c
`;;

let x_truncreverse_mul = `
  !(r:R ring) m p n q.
  ring_polynomial r p ==>
  ring_polynomial r q ==>
  poly_deg r p <= m ==>
  poly_deg r q <= n ==>
  x_truncreverse r (m+n) (poly_mul r p q)
  = poly_mul r (x_truncreverse r m p) (x_truncreverse r n q)
`;;

let x_truncreverse_product = `
  !(r:R ring) n p S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial r (p s)) ==>
  (!s:X. s IN S ==> poly_deg r (p s) <= (n s)) ==>
  x_truncreverse r (nsum S n) (poly_product r S p)
  = poly_product r S (\s. x_truncreverse r (n s) (p s))
`;;

let x_truncreverse_pow = `
  !(r:R ring) p d n.
  ring_polynomial r p ==>
  poly_deg r p <= d ==>
  x_truncreverse r (n*d) (poly_pow r p n)
  = poly_pow r (x_truncreverse r d p) n
`;;

let deg_monic_vanishing_at = `
  !(r:R ring) c:X->R S.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  poly_deg r (monic_vanishing_at r S c)
  = if ring_1 r = ring_0 r then 0 else CARD S
`;;

let deg_monic_vanishing_at_le = `
  !(r:R ring) c:X->R S.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  poly_deg r (monic_vanishing_at r S c)
  <= CARD S
`;;

let topcoeff_monic_vanishing_at = `
  !(r:R ring) c:X->R S.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  coeff (CARD S) (monic_vanishing_at r S c) = ring_1 r
`;;

(* could use HAS_SIZE, RESTRICTED_POWERSET, etc. *)
let coeff_monic_vanishing_at_lemma = `
  !(r:R ring) c:X->R S t n.
  FINITE S ==>
  ~(t IN S) ==>
  (!s:X. s IN t INSERT S ==> c s IN ring_carrier r) ==>
  ~(n = 0) ==>
  n <= CARD S ==>
  ring_add r (
    ring_sum r {U | U SUBSET S /\ CARD U = n} (\U. ring_product r U c)
  ) (
    ring_mul r (c t) (
      ring_sum r {U | U SUBSET S /\ CARD U = n - 1} (\U. ring_product r U c)
    )
  ) =
  ring_sum r {U | U SUBSET t INSERT S /\ CARD U = n} (\U. ring_product r U c)
`;;

let coeff_monic_vanishing_at_lemma2 = `
  !(r:R ring) c:X->R S t n.
  FINITE S ==>
  ~(t IN S) ==>
  (!s:X. s IN t INSERT S ==> c s IN ring_carrier r) ==>
  ~(n = 0) ==>
  n <= CARD S ==>
  ring_sub r (
    ring_mul r (
      ring_pow r (ring_neg r (ring_1 r)) n
    ) (
      ring_sum r {U | U SUBSET S /\ CARD U = n} (\U. ring_product r U c)
    )
  ) (
    ring_mul r (c t) (
      ring_mul r (
        ring_pow r (ring_neg r (ring_1 r)) (n - 1)
      ) (
        ring_sum r {U | U SUBSET S /\ CARD U = n - 1} (\U. ring_product r U c)
      )
    )
  ) =
  ring_mul r (
    ring_pow r (ring_neg r (ring_1 r)) n
  ) (
    ring_sum r {U | U SUBSET t INSERT S /\ CARD U = n} (\U. ring_product r U c)
  )
`;;

let coeff_monic_vanishing_at = `
  !(r:R ring) c:X->R S.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  !n.
  n <= CARD S ==>
  coeff (CARD S - n) (monic_vanishing_at r S c)
  = ring_mul r (
    ring_pow r (ring_neg r (ring_1 r)) n
  ) (
    ring_sum r {U | U SUBSET S /\ CARD U = n} (\U. ring_product r U c)
  )
`;;

let x_truncreverse_monic_vanishing_at = `
  !(r:R ring) c:X->R S.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  x_truncreverse r (CARD S) (monic_vanishing_at r S c)
  = poly_product r S (\s. one_minus_constx r (c s))
`;;

let x_truncreverse_derivative_monic_vanishing_at = `
  !(r:R ring) S c:X->R.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  x_truncreverse r (CARD S - 1)
    (x_derivative r (monic_vanishing_at r S c))
  = poly_sum r S
      (\s. poly_product r (S DELETE s) (\s. one_minus_constx r (c s)))
`;;

let x_truncreverse_subring = `
  !(r:R ring) G n (p:(1->num)->R).
  x_truncreverse (subring_generated r G) n p
  = x_truncreverse r n p
`;;

let botcoeff1_if_x_truncreverse_monic = `
  !(r:R ring) p.
  monic r p ==>
  coeff 0 (x_truncreverse r (poly_deg r p) p) = ring_1 r
`;;

let nonzero_if_x_truncreverse_monic = `
  !(r:R ring) p.
  ~(ring_1 r = ring_0 r) ==>
  monic r p ==>
  ~(x_truncreverse r (poly_deg r p) p = poly_0 r)
`;;

(* ===== newton identities *)

(* (prod_i x_i) sum_i 1/x_i = sum_i prod_(j!=i) x_i *)
let product_times_sum_reciprocals = `
  !(r:R ring) (f:X->R) (g:X->R) S.
  FINITE S ==>
  (!s. s IN S ==> f s IN ring_carrier r) ==>
  (!s. s IN S ==> g s IN ring_carrier r) ==>
  (!s. s IN S ==> ring_mul r (f s) (g s) = ring_1 r) ==>
  ring_mul r
    (ring_product r S (\s. f s))
    (ring_sum r S (\s. g s))
  = ring_sum r S (\t. ring_product r (S DELETE t) (\s. f s))
`;;

let newton_identities_natural = `
  !(r:R ring) c:X->R S.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  poly_mul r
    (poly_product r S (\s. one_minus_constx r (c s)))
    (poly_sum r S (\s. infinite_geometric_series r (c s)))
  = poly_sum r S (\t. poly_product r (S DELETE t) (\s. one_minus_constx r (c s)))
`;;

let newton_identities_monic_vanishing_at = `
  !(r:R ring) c:X->R S.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  poly_mul r
    (x_truncreverse r (CARD S) (monic_vanishing_at r S c))
    (poly_sum r S (\s. infinite_geometric_series r (c s)))
  = x_truncreverse r (CARD S - 1)
      (x_derivative r (monic_vanishing_at r S c))
`;;

(* maybe the most canonical form *)
let newton_identities = `
  !(r:R ring) c:X->R S d.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  ring_sum r (0..d)
    (\a. ring_mul r
      (if a <= CARD S then coeff(CARD S-a) (monic_vanishing_at r S c) else ring_0 r)
      (ring_sum r S (\s. ring_pow r (c s) (d-a)))
    )
  = if d <= CARD S-1 then coeff(CARD S-1-d) (x_derivative r (monic_vanishing_at r S c)) else ring_0 r
`;;

(* pulling out the leading 1 *)
let newton_identities_recurrence = `
  !(r:R ring) c:X->R S d.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  ring_sum r S (\s. ring_pow r (c s) d)
  = ring_sub r
      (if d <= CARD S-1 then coeff(CARD S-1-d) (x_derivative r (monic_vanishing_at r S c)) else ring_0 r)
      (ring_sum r (1..d)
        (\a. ring_mul r
          (if a <= CARD S then coeff(CARD S-a) (monic_vanishing_at r S c) else ring_0 r)
          (ring_sum r S (\s. ring_pow r (c s) (d-a)))
        )
      )
`;;

let powersums_subring_if_poly_subring = `
  !(r:R ring) G S c:X->R d.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  (!n. coeff n (monic_vanishing_at r S c) IN ring_carrier(subring_generated r G)) ==>
  ring_sum r S (\s. ring_pow r (c s) d) IN ring_carrier(subring_generated r G)
`;;

(* the D=1 case boils down to powersums_subring_if_poly_subring_denominators *)
(* but giving shorter proof of that case feels better *)
let powersums_subring_if_poly_subring_denominators_waterfall = `
  !(r:R ring) G S c:X->R D.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  D IN ring_carrier r ==>
  (!i. ring_mul r
         (ring_pow r D i)
         (coeff (CARD S - i) (monic_vanishing_at r S c))
       IN ring_carrier(subring_generated r G)) ==>
  !j.
  ring_mul r
    (ring_pow r D j)
    (ring_sum r S (\s. ring_pow r (c s) j))
  IN ring_carrier(subring_generated r G)
`;;

let powersums_subring_if_poly_subring_denominators = `
  !(r:R ring) G S c:X->R D j.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  D IN ring_carrier r ==>
  (!i. ring_mul r
         (ring_pow r D i)
         (coeff (CARD S - i) (monic_vanishing_at r S c))
       IN ring_carrier(subring_generated r G)) ==>
  ring_mul r
    (ring_pow r D j)
    (ring_sum r S (\s. ring_pow r (c s) j))
  IN ring_carrier(subring_generated r G)
`;;

(* ===== reverse Newton recurrence: coeffs from power sums *)

let newton_identities_reverse = `
  !(r:R ring) c:X->R S n.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  n <= CARD S ==>
  ring_mul r (
    ring_neg r (ring_of_num r n)
  ) (
    coeff(CARD S - n) (monic_vanishing_at r S c)
  )
  =
  ring_sum r (1..n) (\a.
    ring_mul r (
      coeff(CARD S - (n - a)) (monic_vanishing_at r S c)
    ) (
      ring_sum r S (\s. ring_pow r (c s) a)
    )
  )
`;;

let coeff_poly_subring_if_powersums_subring_lemma = `
  !(r:R ring) G S c:X->R.
  ring_hasQ(subring_generated r G) ==>
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  (!d. ring_sum r S (\s. ring_pow r (c s) d) IN ring_carrier(subring_generated r G)) ==>
  !n.
  n <= CARD S ==>
  coeff (CARD S - n) (monic_vanishing_at r S c) IN ring_carrier(subring_generated r G)
`;;

let coeff_poly_subring_if_powersums_subring = `
  !(r:R ring) G S c:X->R.
  ring_hasQ(subring_generated r G) ==>
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  (!d. ring_sum r S (\s. ring_pow r (c s) d) IN ring_carrier(subring_generated r G)) ==>
  !n.
  coeff n (monic_vanishing_at r S c) IN ring_carrier(subring_generated r G)
`;;

let poly_subring_if_powersums_subring = `
  !(r:R ring) G S c:X->R.
  ring_hasQ(subring_generated r G) ==>
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  (!d. ring_sum r S (\s. ring_pow r (c s) d) IN ring_carrier(subring_generated r G)) ==>
  ring_polynomial(subring_generated r G) (monic_vanishing_at r S c)
`;;

let symfun_subring_if_powersums_subring = `
  !(r:R ring) G S c:X->R n.
  ring_hasQ(subring_generated r G) ==>
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  (!d. ring_sum r S (\s. ring_pow r (c s) d) IN ring_carrier(subring_generated r G)) ==>
  ring_sum r {U | U SUBSET S /\ CARD U = n} (\U. ring_product r U c)
  IN ring_carrier(subring_generated r G)
`;;

(* ===== generalized Newton identities for 1/(1-cx)^(e+1) *)
(* note: the e=0 case is given somewhat shorter proofs above *)

let pow_newton_identities_natural = `
  !(r:R ring) c:X->R S e.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  poly_mul r
    (poly_product r S (\s.
       poly_pow r (one_minus_constx r (c s)) (e+1)
    ))
    (poly_sum r S (\s.
       series_from_coeffs (\n.
         ring_mul r
           (ring_of_num r (binom(n+e,e)))
           (ring_pow r (c s) n)
       )
    ))
  = poly_sum r S (\t.
      poly_product r (S DELETE t) (\s.
        poly_pow r (one_minus_constx r (c s)) (e+1)
      )
    )
`;;

let pow_newton_identities_monic_vanishing_at = `
  !(r:R ring) c:X->R S e.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  poly_mul r
    (poly_pow r
      (x_truncreverse r (CARD S) (monic_vanishing_at r S c))
      (e+1)
    )
    (poly_sum r S (\s.
       series_from_coeffs (\n.
         ring_mul r
           (ring_of_num r (binom(n+e,e)))
           (ring_pow r (c s) n)
       )
    ))
  = poly_sum r S (\t.
      poly_product r (S DELETE t) (\s.
        poly_pow r (one_minus_constx r (c s)) (e+1)
      )
    )
`;;

let scaled_pow_newton_identities_monic_vanishing_at_lemma = `
  !(r:R ring) c:X->R S e.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  poly_mul r (
    const_x_pow r (ring_of_num r (FACT(e))) e
  ) (
    poly_sum r S (\s.
      series_from_coeffs (\n.
        ring_mul r
          (ring_of_num r (binom(n+e,e)))
          (ring_pow r (c s) n)
      )
    )
  )
  = poly_sum r S (\s.
      series_from_coeffs (\n.
        ring_mul r
          (ring_of_num r (FACT(e) * binom(n,e)))
          (ring_pow r (c s) (n-e))
      )
    )
`;;

let scaled_pow_newton_rightside = new_definition `
  scaled_pow_newton_rightside (r:R ring) (c:X->R) (S:X->bool) (e:num)
  = poly_mul r (
      const_x_pow r (ring_of_num r (FACT(e))) e
    ) (
      poly_sum r S (\t.
        poly_product r (S DELETE t) (\s.
          poly_pow r (one_minus_constx r (c s)) (e+1)
        )
      )
    )
`;;

let scaled_pow_newton_identities_monic_vanishing_at = `
  !(r:R ring) c:X->R S e.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  poly_mul r
    (poly_pow r
      (x_truncreverse r (CARD S) (monic_vanishing_at r S c))
      (e+1)
    )
    (poly_sum r S (\s.
       series_from_coeffs (\n.
         ring_mul r
           (ring_of_num r (FACT(e) * binom(n,e)))
           (ring_pow r (c s) (n-e))
       )
    ))
  = scaled_pow_newton_rightside r c S e
`;;

let poly_pow_newton_identities_monic_vanishing_at_lemma = `
  !(r:R ring) c:X->R S e t.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  t IN S ==>
  ring_polynomial(r:R ring) (poly_product r (S DELETE t) (\s. poly_pow r (one_minus_constx r (c s)) (e + 1)))
`;;

let poly_pow_newton_identities_monic_vanishing_at = `
  !(r:R ring) c:X->R S e.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  ring_polynomial r (
    poly_sum r S (\t.
      poly_product r (S DELETE t) (\s.
        poly_pow r (one_minus_constx r (c s)) (e+1)
      )
    )
  )
`;;

let poly_scaled_pow_newton_rightside = `
  !(r:R ring) c:X->R S e.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  ring_polynomial r (scaled_pow_newton_rightside r c S e)
`;;

let deg_pow_newton_identities_monic_vanishing_at_lemma = `
  !(r:R ring) c:X->R S e t.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  t IN S ==>
  poly_deg(r:R ring) (poly_product r (S DELETE t) (\s. poly_pow r (one_minus_constx r (c s)) (e + 1))) <= (CARD S - 1) * (e+1)
`;;

let deg_pow_newton_identities_monic_vanishing_at = `
  !(r:R ring) c:X->R S e.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  poly_deg r (
    poly_sum r S (\t.
      poly_product r (S DELETE t) (\s.
        poly_pow r (one_minus_constx r (c s)) (e+1)
      )
    )
  )
  <= (CARD S - 1) * (e+1)
`;;

let deg_scaled_pow_newton_rightside = `
  !(r:R ring) c:X->R S e.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  poly_deg r (scaled_pow_newton_rightside r c S e)
  <= e + (CARD S - 1) * (e+1)
`;;

(* ===== the ring of complex numbers *)

let complex_ring = new_definition `
  complex_ring = ring((:complex),Cx(&0),Cx(&1),( -- ),( + ),( * ))
`;;

let complex_of_num = new_definition `
  complex_of_num(n:num) = Cx(real_of_num n)
`;;

let complex_of_int = new_definition `
  complex_of_int(n:int) = Cx(real_of_int n)
`;;

let complex_ring_clauses = `ring_carrier complex_ring = (:complex) /\
   ring_0 complex_ring = Cx(&0) /\
   ring_1 complex_ring = Cx(&1) /\
   ring_neg complex_ring = ( -- ) /\
   ring_add complex_ring = ( + ) /\
   ring_mul complex_ring = ( * )`;;

let in_complex_ring = `
  !z.
  z IN ring_carrier complex_ring
`;;

let field_complex = `
  field complex_ring
`;;

let integral_domain_complex = `
  integral_domain complex_ring
`;;

let ring_of_num_complex = `
  ring_of_num complex_ring = complex_of_num
`;;

let ring_of_int_complex = `
  ring_of_int complex_ring = complex_of_int
`;;

let ring_char_complex = `
  ring_char complex_ring = 0
`;;

let ring_sub_complex = `
  ring_sub complex_ring = (-)
`;;

(* from Complex/complexnumbers.ml *)
let COMPLEX_MUL_RINV_UNIQ = `!w z. w * z = Cx(&1) ==> inv w = z`;;

let ring_inv_complex = `
  ring_inv complex_ring = inv
`;;

let ring_div_complex = `
  ring_div complex_ring = (/)
`;;

let ring_pow_complex = `
  ring_pow complex_ring = (pow)
`;;

let complex_field_clauses = `ring_carrier complex_ring = (:complex) /\
   ring_0 complex_ring = Cx(&0) /\
   ring_1 complex_ring = Cx(&1) /\
   ring_neg complex_ring = ( -- ) /\
   ring_add complex_ring = ( + ) /\
   ring_mul complex_ring = ( * ) /\
   ring_of_num complex_ring = complex_of_num /\
   ring_sub complex_ring = (-) /\
   ring_inv complex_ring = inv /\
   ring_div complex_ring = (/) /\
   ring_pow complex_ring = (pow)`;;

let vsum_ring_sum_complex = `
  !(f:X->complex) S.
  FINITE S ==>
  vsum S f =
  ring_sum complex_ring S f
`;;

let cproduct_ring_product_complex = `
  !(f:X->complex) S.
  FINITE S ==>
  cproduct S f =
  ring_product complex_ring S f
`;;

let vsum_delta_complex = `
  !(S:X->bool) t a.
  FINITE S ==>
  vsum S (\s. if s = t then a else Cx(&0))
  = if t IN S then a else Cx(&0)
`;;

let ring_1_0_complex = `
  ~(ring_1 complex_ring = ring_0 complex_ring)
`;;

(* ===== \C[x] *)

let series_complex = `
  !(p:(1->num)->complex).
  ring_powerseries complex_ring p
`;;

let complex_coeff_x_pow_times = `
  !d p e.
  coeff e (poly_mul complex_ring (x_pow complex_ring d) p)
  = if e < d then Cx(&0) else coeff (e - d) p
`;;

let poly_1_0_complex = `
  ~(poly_1 complex_ring = poly_0 complex_ring:(V->num)->complex)
`;;

(* ===== copy of \Z inside \C *)

let ZinC = new_definition `
  ZinC = {z:complex | ?i:int. z = complex_of_int i}
`;;

let ZinC_ring = new_definition `
  ZinC_ring = ring(ZinC,Cx(&0),Cx(&1),( -- ),( + ),( * ))
`;;

let ii_not_in_ZinC = `
  ~(ii IN ZinC)
`;;

let half_not_in_ZinC = `
  ~(Cx(&1 / &2) IN ZinC)
`;;

let num_in_ZinC = `
  !d. Cx(&d) IN ZinC
`;;

let int_in_ZinC = `
  !i. complex_of_int i IN ZinC
`;;

let ZinC_0 = `
  Cx(&0) IN ZinC
`;;

let ZinC_1 = `
  Cx(&1) IN ZinC
`;;

let neg_in_ZinC = `
  !x:complex.
  x IN ZinC ==> --x IN ZinC
`;;

let add_in_ZinC = `
  !x:complex y:complex.
  x IN ZinC /\ y IN ZinC ==> x+y IN ZinC
`;;

let mul_in_ZinC = `
  !x:complex y:complex.
  x IN ZinC /\ y IN ZinC ==> x*y IN ZinC
`;;

let ZinC_ring_clauses = `
  ring_carrier ZinC_ring = ZinC /\
  ring_0 ZinC_ring = Cx(&0) /\
  ring_1 ZinC_ring = Cx(&1) /\
  ring_neg ZinC_ring = ( -- ) /\
  ring_add ZinC_ring = ( + ) /\
  ring_mul ZinC_ring = ( * )
`;;

let ZinC_subring_complex = `
  ZinC subring_of complex_ring
`;;

let ZinC_subring_generated_carrier = `
  ZinC = INTERS {S | S subring_of complex_ring}
`;;

let subring_complex_empty_lemma = `
  INTERS {S | S subring_of complex_ring /\ (:complex) INTER {} SUBSET S} = ZinC
`;;

let subring_complex_empty = `
  subring_generated complex_ring {} = ZinC_ring
`;;

let ring_char_ZinC = `
  ring_char ZinC_ring = 0
`;;

let subring_complex_ZinC_lemma = `
  INTERS {S | S subring_of complex_ring /\ (:complex) INTER ZinC SUBSET S} = ZinC
`;;

let subring_complex_ZinC = `
  subring_generated complex_ring ZinC = ZinC_ring
`;;

let ring_of_num_ZinC = `
  ring_of_num ZinC_ring = complex_of_num
`;;

let ring_pow_ZinC = `
  ring_pow ZinC_ring = (pow)
`;;

let integral_domain_ZinC = `
  integral_domain ZinC_ring
`;;

(* ===== \Z[x] *)

let poly_complex_if_poly_ZinC = `
  !p:(V->num)->complex.
  ring_polynomial ZinC_ring p ==>
  ring_polynomial complex_ring p
`;;

let poly_0_ZinC_eq_poly_0_complex = `
  poly_0 ZinC_ring = (poly_0 complex_ring):(V->num)->complex
`;;

let zero_if_ZinC_norm_lt1 = `
  !z.
  z IN ZinC ==>
  norm z < &1 ==>
  z = Cx(&0)
`;;

let zero_if_ZinC_scale_bound = `
  !(c:complex) (r:real) z.
  ~(c = Cx(&0)) ==>
  c * z IN ZinC ==>
  norm z <= r ==>
  norm c * r < &1 ==>
  z = Cx(&0)
`;;

(* ===== copy of \Q inside \C *)

let QinC = new_definition `
  QinC = {z:complex | ?i:int d:num. ~(d = 0) /\ Cx(&d) * z = complex_of_int i}
`;;

let QinC_ring = new_definition `
  QinC_ring = ring(QinC,Cx(&0),Cx(&1),( -- ),( + ),( * ))
`;;

let ZinC_in_QinC = `
  !z. z IN ZinC ==> z IN QinC
`;;

let ZinC_subset_QinC = `
  ZinC SUBSET QinC
`;;

let QinC_0 = `
  Cx(&0) IN QinC
`;;

let QinC_1 = `
  Cx(&1) IN QinC
`;;

let neg_in_QinC = `
  !z. z IN QinC ==> --z IN QinC
`;;

let add_in_QinC = `
  !y z.
  y IN QinC /\ z IN QinC ==>
  y+z IN QinC
`;;

let mul_in_QinC = `
  !y z.
  y IN QinC /\ z IN QinC ==>
  y*z IN QinC
`;;

let QinC_ring_clauses = `
  ring_carrier QinC_ring = QinC /\
  ring_0 QinC_ring = Cx(&0) /\
  ring_1 QinC_ring = Cx(&1) /\
  ring_neg QinC_ring = ( -- ) /\
  ring_add QinC_ring = ( + ) /\
  ring_mul QinC_ring = ( * )
`;;

let ZinC_subring_QinC = `
  ZinC subring_of QinC_ring
`;;

let QinC_subring_complex = `
  QinC subring_of complex_ring
`;;

let series_QinC_if_series_ZinC = `
  !p:(V->num)->complex.
  ring_powerseries ZinC_ring p ==>
  ring_powerseries QinC_ring p
`;;

let poly_QinC_if_poly_ZinC = `
  !p:(V->num)->complex.
  ring_polynomial ZinC_ring p ==>
  ring_polynomial QinC_ring p
`;;

let poly_complex_if_poly_QinC = `
  !p:(V->num)->complex.
  ring_polynomial QinC_ring p ==>
  ring_polynomial complex_ring p
`;;

let series_complex_if_series_QinC = `
  !p:(V->num)->complex.
  ring_powerseries QinC_ring p ==>
  ring_powerseries complex_ring p
`;;

let poly_0_QinC_eq_poly_0_complex = `
  poly_0 QinC_ring = (poly_0 complex_ring):(V->num)->complex
`;;

let poly_1_QinC_eq_poly_1_complex = `
  poly_1 QinC_ring = (poly_1 complex_ring):(V->num)->complex
`;;

let poly_neg_QinC_eq_poly_neg_complex = `
  !p:(V->num)->complex.
  poly_neg QinC_ring p
  = poly_neg complex_ring p
`;;

let poly_add_QinC_eq_poly_add_complex = `
  !p:(V->num)->complex q.
  poly_add QinC_ring p q
  = poly_add complex_ring p q
`;;

let x_pow_QinC_eq_x_pow_complex = `
  !n.
  x_pow QinC_ring n = x_pow complex_ring n
`;;

let poly_0_ZinC_eq_poly_0_QinC = `
  poly_0 ZinC_ring = (poly_0 QinC_ring):(V->num)->complex
`;;

let ring_of_num_QinC = `
  ring_of_num QinC_ring = complex_of_num
`;;

let num_in_QinC = `
  !n. Cx(&n) IN QinC
`;;

let num_over_num_in_QinC = `
  !n d. Cx(&n) / Cx(&d) IN QinC
`;;

let neg_num_over_num_in_QinC = `
  !n d. -- (Cx(&n) / Cx(&d)) IN QinC
`;;

let field_QinC = `
  field QinC_ring
`;;

let integral_domain_QinC = `
  integral_domain QinC_ring
`;;

let QinC_over_num = `
  !z e.
  z IN QinC ==>
  ~(e = 0) ==>
  z / Cx(&e) IN QinC
`;;

let div_in_QinC = `
  !y z.
  y IN QinC /\ z IN QinC /\ ~(z = Cx(&0)) ==>
  y/z IN QinC
`;;

let QinC_to_ZinC = `
  !z.
  z IN QinC ==>
  ?d. (~(d = 0) /\ Cx(&d) * z IN ZinC)
`;;

let multi_QinC_to_ZinC = `
  !S f:X->complex.
  FINITE S ==>
  (!s. s IN S ==> f s IN QinC) ==>
  ?d. (~(d = 0) /\ !s. s IN S ==> Cx(&d) * f s IN ZinC)
`;;

let subring_complex_QinC_lemma = `
  INTERS {S | S subring_of complex_ring /\ (:complex) INTER QinC SUBSET S} = QinC
`;;

let subring_complex_QinC = `
  subring_generated complex_ring QinC = QinC_ring
`;;

let ring_char_QinC = `
  ring_char QinC_ring = 0
`;;

let ring_hasQ_QinC = `
  ring_hasQ QinC_ring
`;;

let ring_sub_QinC = `
  ring_sub QinC_ring = (-)
`;;

let x_minus_const_QinC_eq_x_minus_const_complex = `
  !c.
  x_minus_const QinC_ring c = x_minus_const complex_ring c
`;;

let subring_QinC_empty_lemma = `
  INTERS {S | S subring_of QinC_ring /\ QinC INTER {} SUBSET S} = ZinC
`;;

let subring_QinC_empty = `
  subring_generated QinC_ring {} = ZinC_ring
`;;

let ring_1_0_QinC = `
  ~(ring_1 QinC_ring = ring_0 QinC_ring)
`;;

let ring_pow_QinC = `
  ring_pow QinC_ring = (pow)
`;;

let sum_QinC_eq_sum_complex = `
  !S f.
  (!s:X. s IN S ==> f s IN QinC) ==>
  ring_sum QinC_ring S f
  = ring_sum complex_ring S f
`;;

let poly_mul_QinC_eq_poly_mul_complex = `
  !p:(V->num)->complex q.
  ring_powerseries QinC_ring p ==>
  ring_powerseries QinC_ring q ==>
  poly_mul QinC_ring p q
  = poly_mul complex_ring p q
`;;

let ring_divides_poly_complex_if_ring_divides_poly_QinC = `
  !p:(1->num)->complex q.
  ring_divides(x_poly QinC_ring) p q ==>
  ring_divides(x_poly complex_ring) p q
`;;

(* ===== \Q[x] *)

let PID_x_poly_QinC = `
  PID (x_poly QinC_ring)
`;;

let integral_domain_x_poly_QinC = `
  integral_domain (x_poly QinC_ring)
`;;

let UFD_x_poly_QinC = `
  UFD (x_poly QinC_ring)
`;;

let x_poly_mul_in_QinC_eq_0 = `
  !(p:(1->num)->complex) (q:(1->num)->complex).
  ring_polynomial QinC_ring p ==>
  ring_polynomial QinC_ring q ==>
  (poly_mul QinC_ring p q = poly_0 QinC_ring
   <=> p = poly_0 QinC_ring \/ q = poly_0 QinC_ring)
`;;

let x_poly_ZinC_denominator_is_QinC = `
  !(p:(1->num)->complex) e.
  ring_polynomial ZinC_ring p ==>
  ~(e = 0) ==>
  ring_polynomial QinC_ring
    (series_from_coeffs (\n. (coeff n p) / Cx(&e)))
`;;

let x_poly_ZinC_denominator_is_QinC_v2_lemma = `
  !(p:(1->num)->complex) e.
  series_from_coeffs (\n. (coeff n p) / Cx(&e))
  = poly_mul complex_ring (poly_const complex_ring (Cx(&1) / Cx(&e))) p
`;;

let poly_const_QinC = `
  !c.
  c IN QinC <=>
  ring_polynomial QinC_ring (poly_const QinC_ring c:(V->num)->complex)
`;;

let poly_const_QinC_poly_const_complex = `
  !c.
  poly_const QinC_ring c
  = poly_const complex_ring c:(V->num)->complex
`;;

let poly_mul_QinC_poly_mul_complex = `
  !(p:(1->num)->complex) (q:(1->num)->complex).
  ring_powerseries QinC_ring p ==>
  ring_powerseries QinC_ring q ==>
  poly_mul QinC_ring p q
  = poly_mul complex_ring p q
`;;

let x_poly_ZinC_denominator_is_QinC_v2_lemma2 = `
  !(p:(1->num)->complex) e.
  ring_powerseries QinC_ring p ==>
  series_from_coeffs (\n. (coeff n p) / Cx(&e))
  = poly_mul QinC_ring (poly_const QinC_ring (Cx(&1) / Cx(&e))) p
`;;

let x_poly_ZinC_denominator_is_QinC_v2 = `
  !(p:(1->num)->complex) e.
  ring_polynomial ZinC_ring p ==>
  ~(e = 0) ==>
  ring_polynomial QinC_ring
    (poly_mul QinC_ring (poly_const QinC_ring (Cx(&1) / Cx(&e))) p)
`;;

(* XXX: should factor proof through multi_QinC_to_ZinC *)
let x_poly_QinC_is_ZinC_denominator = `
  !p:(1->num)->complex.
  ring_polynomial QinC_ring p ==>
  ?e. (~(e = 0) /\
       ring_polynomial ZinC_ring
         (series_from_coeffs (\n. Cx(&e) * coeff n p))
      )
`;;

let x_poly_QinC_is_ZinC_denominator_v2_lemma = `
  !(p:(1->num)->complex) e.
  series_from_coeffs (\n. Cx(&e) * coeff n p)
  = poly_mul complex_ring (poly_const complex_ring (Cx(&e))) p
`;;

let x_poly_QinC_is_ZinC_denominator_v2_lemma2 = `
  !(p:(1->num)->complex) e.
  ring_powerseries QinC_ring p ==>
  series_from_coeffs (\n. Cx(&e) * coeff n p)
  = poly_mul QinC_ring (poly_const QinC_ring (Cx(&e))) p
`;;

let x_poly_QinC_is_ZinC_denominator_v2 = `
  !p:(1->num)->complex.
  ring_polynomial QinC_ring p ==>
  ?e. (~(e = 0) /\
       ring_polynomial ZinC_ring
         (poly_mul QinC_ring (poly_const QinC_ring (Cx(&e))) p)
      )
`;;

let ring_hasQ_subring_series_complex = `
  ring_hasQ (
    subring_generated (
      x_series complex_ring
    ) (
      ring_carrier (x_series QinC_ring)
    )
  )
`;;

(* ===== algebraic numbers *)

let algebraic_number = new_definition `
  algebraic_number (z:complex)
  <=> ?p. (ring_polynomial ZinC_ring p
           /\ ~(p = poly_0 ZinC_ring)
           /\ poly_eval complex_ring p z = Cx(&0)
          )
`;;

let algebraic_number_ZinC_explicit = `
  !z.
  z IN ZinC ==> (
    ring_polynomial ZinC_ring (x_minus_const ZinC_ring z) /\
    ~((x_minus_const ZinC_ring z) = poly_0 ZinC_ring) /\
    poly_eval complex_ring (x_minus_const ZinC_ring z) z = Cx(&0)
  )
`;;

let algebraic_number_ZinC = `
  !z.
  z IN ZinC ==> algebraic_number z
`;;

let algebraic_number_ii = `
  algebraic_number ii
`;;

let algebraic_number_half = `
  algebraic_number (Cx(&1 / &2))
`;;

let algebraic_number_if_monic_vanishing_at = `
  !S (c:X->complex) s.
  FINITE S ==>
  ring_polynomial ZinC_ring (monic_vanishing_at complex_ring S c) ==>
  s IN S ==>
  algebraic_number (c s)
`;;

(* ===== algebraic numbers via \Q[x] *)

let algebraic_number_root_QinC_poly = `
  !z:complex.
  algebraic_number z
  <=> ?p. (ring_polynomial QinC_ring p
           /\ ~(p = poly_0 QinC_ring)
           /\ poly_eval complex_ring p z = Cx(&0)
          )
`;;

let algebraic_number_if_monic_vanishing_at_QinC = `
  !S (c:X->complex) s.
  FINITE S ==>
  ring_polynomial QinC_ring (monic_vanishing_at complex_ring S c) ==>
  s IN S ==>
  algebraic_number (c s)
`;;

let algebraic_number_if_root_irreducible_QinC_poly = `
  !z:complex.
  (?p. (ring_polynomial QinC_ring p
        /\ ring_irreducible(x_poly QinC_ring) p
        /\ poly_eval complex_ring p z = Cx(&0)
       )
  ) ==> algebraic_number z
`;;

let algebraic_number_is_root_irreducible_QinC_poly = `
  !z:complex.
  algebraic_number z
  ==> ?p. (ring_polynomial QinC_ring p
           /\ ~(p = poly_0 QinC_ring)
           /\ ring_irreducible(x_poly QinC_ring) p
           /\ poly_eval complex_ring p z = Cx(&0)
          )
`;;

let algebraic_number_root_irreducible_QinC_poly = `
  !z:complex.
  algebraic_number z
  <=> ?p. (ring_polynomial QinC_ring p
           /\ ~(p = poly_0 QinC_ring)
           /\ ring_irreducible(x_poly QinC_ring) p
           /\ poly_eval complex_ring p z = Cx(&0)
          )
`;;

let algebraic_number_is_root_monic_irreducible_QinC_poly = `
  !z:complex.
  algebraic_number z
  ==> ?p. (ring_polynomial QinC_ring p
           /\ ~(p = poly_0 QinC_ring)
           /\ monic QinC_ring p
           /\ ring_irreducible(x_poly QinC_ring) p
           /\ poly_eval complex_ring p z = Cx(&0)
          )
`;;

let coprimes_sharing_root = `
  !(r:R ring) s G p q z.
  s = subring_generated r G ==>
  field s ==>
  ring_polynomial s p ==>
  ring_polynomial s q ==>
  ~(p = poly_0 s) ==>
  ~(q = poly_0 s) ==>
  ring_irreducible(x_poly s) p ==>
  ring_irreducible(x_poly s) q ==>
  z IN ring_carrier r ==>
  poly_eval r p z = ring_0 r ==>
  poly_eval r q z = ring_0 r ==>
  ring_associates(x_poly s) p q
`;;

let algebraic_number_is_root_unique_monic_irreducible_QinC_poly_lemma = `
  !(z:complex) p q.
  ring_polynomial QinC_ring p
  /\ ring_polynomial QinC_ring q
  /\ ~(p = poly_0 QinC_ring)
  /\ ~(q = poly_0 QinC_ring)
  /\ ring_irreducible(x_poly QinC_ring) p
  /\ ring_irreducible(x_poly QinC_ring) q
  /\ poly_eval complex_ring p z = Cx(&0)
  /\ poly_eval complex_ring q z = Cx(&0)
  ==> ring_associates(x_poly QinC_ring) p q
`;;

let algebraic_number_is_root_unique_monic_irreducible_QinC_poly_simple = `
  !(z:complex) p q.
  ring_polynomial QinC_ring p
  /\ ring_polynomial QinC_ring q
  /\ ~(p = poly_0 QinC_ring)
  /\ ~(q = poly_0 QinC_ring)
  /\ monic QinC_ring p
  /\ monic QinC_ring q
  /\ ring_irreducible(x_poly QinC_ring) p
  /\ ring_irreducible(x_poly QinC_ring) q
  /\ poly_eval complex_ring p z = Cx(&0)
  /\ poly_eval complex_ring q z = Cx(&0)
  ==> p = q
`;;

let algebraic_number_is_root_unique_monic_irreducible_QinC_poly = `
  !z:complex.
  algebraic_number z
  ==> ?!p. (ring_polynomial QinC_ring p
            /\ ~(p = poly_0 QinC_ring)
            /\ monic QinC_ring p
            /\ ring_irreducible(x_poly QinC_ring) p
            /\ poly_eval complex_ring p z = Cx(&0)
           )
`;;

let algebraic_number_QinC_explicit = `
  !z.
  z IN QinC ==> (
    ring_polynomial QinC_ring (x_minus_const QinC_ring z) /\
    ~((x_minus_const QinC_ring z) = poly_0 QinC_ring) /\
    monic QinC_ring (x_minus_const QinC_ring z) /\
    ring_irreducible (x_poly QinC_ring) (x_minus_const QinC_ring z) /\
    poly_eval complex_ring (x_minus_const QinC_ring z) z = Cx(&0)
  )
`;;

let algebraic_number_QinC = `
  !z.
  z IN QinC ==> algebraic_number z
`;;

(* ===== minimal polynomials *)

let minimal_polynomial = new_definition `
  minimal_polynomial (z:complex) =
  if algebraic_number z
  then (@p. (ring_polynomial QinC_ring p
             /\ ~(p = poly_0 QinC_ring)
             /\ monic QinC_ring p
             /\ ring_irreducible(x_poly QinC_ring) p
             /\ poly_eval complex_ring p z = Cx(&0)
            ))
  else poly_0 QinC_ring
`;;

let algebraic_has_minimal_polynomial = `
  !z:complex.
  algebraic_number z ==>
  ring_polynomial QinC_ring (minimal_polynomial z)
  /\ ~((minimal_polynomial z) = poly_0 QinC_ring)
  /\ monic QinC_ring (minimal_polynomial z)
  /\ ring_irreducible(x_poly QinC_ring) (minimal_polynomial z)
  /\ poly_eval complex_ring (minimal_polynomial z) z = Cx(&0)
`;;

let maybe_algebraic_minimal_polynomial = `
  !z:complex.
  ring_polynomial QinC_ring (minimal_polynomial z)
  /\ poly_eval complex_ring (minimal_polynomial z) z = Cx(&0)
`;;

let minimal_polynomial_QinC = `
  !z:complex.
  z IN QinC ==>
  minimal_polynomial z = x_minus_const QinC_ring z
`;;

(* ===== using fundamental theorem of algebra *)

let poly_eval_vsum_lemma = `
  !(p:(1->num)->complex) z n.
  vsum (0..n) (\i. coeff i p * z pow i)
  = ring_sum complex_ring (0..n)
      (\d. ring_mul complex_ring (coeff d p) (ring_pow complex_ring z d))
`;;

let poly_eval_vsum = `
  !(p:(1->num)->complex) z n.
  ring_polynomial complex_ring p ==>
  poly_deg complex_ring p <= n ==>
  vsum (0..n) (\i. coeff i p * z pow i)
  = poly_eval complex_ring p z
`;;

let nonconstant_complex_root = `
  !p:(1->num)->complex.
  ring_polynomial complex_ring p ==>
  1 <= poly_deg complex_ring p ==>
  ?z. poly_eval complex_ring p z = Cx(&0)
`;;

let nonconstant_complex_x_minus_root = `
  !p:(1->num)->complex.
  ring_polynomial complex_ring p ==>
  1 <= poly_deg complex_ring p ==>
  ?z q. ring_polynomial complex_ring q /\ p = poly_mul complex_ring (x_minus_const complex_ring z) q
`;;

let associates_monic_vanishing_at_if_complex_lemma = `
  !n (p:(1->num)->complex).
  ring_polynomial complex_ring p ==>
  ~(p = poly_0 complex_ring) ==>
  poly_deg complex_ring p = n ==>
  ?c. ring_associates(x_poly complex_ring)
        p
        (monic_vanishing_at complex_ring {i:num | i < n} c)
`;;

let associates_monic_vanishing_at_if_complex = `
  !p:(1->num)->complex.
  ring_polynomial complex_ring p ==>
  ~(p = poly_0 complex_ring) ==>
  ?c. ring_associates(x_poly complex_ring)
        p
        (monic_vanishing_at complex_ring {i:num | i < poly_deg complex_ring p} c)
`;;

let monic_vanishing_at_if_monic_complex = `
  !p:(1->num)->complex.
  ring_polynomial complex_ring p ==>
  monic complex_ring p ==>
  ?c. p = monic_vanishing_at complex_ring {i | i < poly_deg complex_ring p} c
`;;

let monic_QinC_squarefree_complex_squarefree_lemma = `
  !(r:R ring) C p qpd qp'd D:(1->num)->R.
  ring_polynomial r C ==>
  ring_polynomial r p ==>
  ring_polynomial r qpd ==>
  ring_polynomial r qp'd ==>
  ring_polynomial r D ==>
  p = poly_mul r C qpd ==>
  poly_mul r C qp'd = poly_add r qpd (poly_mul r C D) ==>
  p = poly_mul r (poly_mul r C C) (poly_sub r qp'd D)
`;;

(* XXX: should write this for more general field extensions *)
(* XXX: and should do more elementary proof via gcd computation being preserved by field extensions *)
(* XXX: e.g., formulate via resultants *)
let monic_QinC_squarefree_complex_squarefree = `
  !p:(1->num)->complex.
  ring_polynomial QinC_ring p ==>
  monic QinC_ring p ==>
  (ring_squarefree(x_poly QinC_ring) p <=>
   ring_squarefree(x_poly complex_ring) p)
`;;

let monic_squarefree_complex_roots = `
  !p:(1->num)->complex.
  ring_polynomial complex_ring p ==>
  ring_squarefree(x_poly complex_ring) p ==>
  monic complex_ring p ==>
  ?S. FINITE S /\ p = monic_vanishing_at complex_ring S I
`;;

let QinC_monic_irreducible_complex_roots = `
  !p:(1->num)->complex.
  ring_polynomial QinC_ring p ==>
  ring_irreducible(x_poly QinC_ring) p ==>
  monic QinC_ring p ==>
  ?S. FINITE S /\ p = monic_vanishing_at complex_ring S I
`;;

(* ===== complex_root *)

let complex_root = new_definition `
  complex_root p (z:complex)
  <=> poly_eval complex_ring p z = Cx(&0)
`;;

let complex_root_ring = `
  !p z.
  complex_root p z
  <=> poly_eval complex_ring p z = ring_0 complex_ring
`;;

let complex_root_divides = `
  !p q.
  ring_divides(x_poly complex_ring) p q
  ==> complex_root p SUBSET complex_root q
`;;

let complex_root_associates = `
  !p q.
  ring_associates(x_poly complex_ring) p q
  ==> complex_root p = complex_root q
`;;

let complex_root_le_deg = `
  !p.
  ring_polynomial complex_ring p ==>
  ~(p = poly_0 complex_ring) ==>
  (FINITE(complex_root p)
   /\ CARD(complex_root p) <= poly_deg complex_ring p
  )
`;;

let complex_root_monic_vanishing_at = `
  !S.
  FINITE S ==>
  complex_root (monic_vanishing_at complex_ring S I) = S
`;;

let monic_vanishing_at_complex_root = `
  !p.
  ring_polynomial complex_ring p ==>
  ring_squarefree(x_poly complex_ring) p ==>
  monic complex_ring p ==>
  monic_vanishing_at complex_ring (complex_root p) I = p
`;;

let complex_root_if_x_minus_const_divides = `
  !p z.
  ring_divides(x_poly complex_ring) (x_minus_const complex_ring z) p ==>
  complex_root p z
`;;

let complex_root_x_pow = `
  !n.
  complex_root(x_pow QinC_ring n)
  = if n = 0 then {} else {Cx(&0)}
`;;

let complex_root_x_minus_const = `
  !c.
  complex_root(x_minus_const complex_ring c)
  = {c}
`;;

let not_coprime_QinC_if_shared_complex_root = `
  !z:complex p q.
  complex_root p z ==>
  complex_root q z ==>
  ~(ring_coprime(x_poly QinC_ring) (p,q))
`;;

let complex_root_minimal_polynomial_refl = `
  !z:complex.
  complex_root (minimal_polynomial z) z
`;;

let minimal_polynomial_divides = `
  !z:complex p:(1->num)->complex.
  algebraic_number z ==>
  ring_polynomial QinC_ring p ==>
  ( ring_divides(x_poly QinC_ring) (minimal_polynomial z) p
    <=> complex_root p z
  )
`;;

(* ===== complex_root_powersums: sum_{z:p(z)=0} z^n *)

let complex_root_powersums = new_definition `
  complex_root_powersums p n
  = ring_sum complex_ring (complex_root p) (\z. z pow n)
`;;

let complex_root_powersums_ring = `
  !p n.
  complex_root_powersums p n
  = ring_sum complex_ring (complex_root p) (\z. ring_pow complex_ring z n)
`;;

let complex_root_powersums_QinC_monic_irreducible_QinC = `
  !(p:(1->num)->complex) n.
  ring_polynomial QinC_ring p ==>
  ring_irreducible(x_poly QinC_ring) p ==>
  monic QinC_ring p ==>
  complex_root_powersums p n IN QinC
`;;

(*
Another way to prove the following:
prove complex_root_powersums_ZinC_monic_irreducible_ZinC
(as in complex_root_powersums_ZinC_monic_irreducible_ZinC,
plus relating ZinC irreducibles to QinC irreducibles)
and then multiply each root by D to reduce to that case.

Alternatively, after proving this, can specialize to Z=1
to prove complex_root_powersums_ZinC_monic_irreducible_ZinC.

Yet another way,
after showing that algebraic integers form a ring:
Dz is an algebraic integer for each z
so sum_z (Dz)^n is an algebraic integer
but D^n sum_z z^n is rational, ergo integer.
This again boils down to Newton's identities.
*)
let complex_root_powersums_QinC_monic_irreducible_ZinC = `
  !(p:(1->num)->complex) D n.
  ring_polynomial QinC_ring p ==>
  ring_irreducible(x_poly QinC_ring) p ==>
  monic QinC_ring p ==>
  (!i. D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  D pow n * complex_root_powersums p n IN ZinC
`;;

(* ===== denominators of monic polys *)
(* meaning: D where all D^i p_(deg p - i) are integers *)
(* equivalently: Dz is algebraic integer for each root z *)

let denominator_if_monic_QinC = `
  !(p:(1->num)->complex).
  ring_polynomial QinC_ring p ==>
  monic QinC_ring p ==>
  ?D. D IN ZinC /\
      ~(D = Cx(&0)) /\
      (!i. D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC)
`;;

let denominator_reverse = `
  !(p:(1->num)->complex).
  ring_polynomial QinC_ring p ==>
  monic QinC_ring p ==>
  (!i. D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  (!i. D pow i * (coeff i (x_truncreverse QinC_ring (poly_deg complex_ring p) p)) IN ZinC)
`;;

let denominator_reverse_mul = `
  !(p:(1->num)->complex) q D.
  ring_powerseries QinC_ring p ==>
  ring_powerseries QinC_ring q ==>
  D IN ZinC ==>
  (!i. D pow i * (coeff i p) IN ZinC) ==>
  (!i. D pow i * (coeff i q) IN ZinC) ==>
  (!i. D pow i * (coeff i (poly_mul QinC_ring p q)) IN ZinC)
`;;

let denominator_reverse_product = `
  !p D (S:X->bool).
  FINITE S ==>
  (!s. s IN S ==> ring_powerseries QinC_ring (p s)) ==>
  D IN ZinC ==>
  (!s i. s IN S ==> D pow i * (coeff i (p s)) IN ZinC) ==>
  (!i. D pow i * (coeff i (poly_product QinC_ring S p)) IN ZinC)
`;;

let denominator_reverse_pow = `
  !p D n.
  ring_powerseries QinC_ring p ==>
  D IN ZinC ==>
  (!i. D pow i * (coeff i p) IN ZinC) ==>
  (!i. D pow i * (coeff i (poly_pow QinC_ring p n)) IN ZinC)
`;;

(* ===== distinct minpolys *)

let distinct_minpolys = new_definition `
  distinct_minpolys P <=>
  !p. p IN P ==>
  (ring_polynomial QinC_ring p
   /\ ring_irreducible(x_poly QinC_ring) p
   /\ monic QinC_ring p
  )
`;;

let polynomial_product_distinct_minpolys = `
  !P.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_polynomial QinC_ring (poly_product QinC_ring P I)
`;;

let monic_product_distinct_minpolys = `
  !P.
  FINITE P ==>
  distinct_minpolys P ==>
  monic QinC_ring (poly_product QinC_ring P I)
`;;

let distinct_minpolys_nonzero = `
  !P p.
  distinct_minpolys P ==>
  p IN P ==>
  ~(p = poly_0 QinC_ring)
`;;

let distinct_minpolys_reverse_nonzero = `
  !P p.
  distinct_minpolys P ==>
  p IN P ==>
  ~(x_truncreverse QinC_ring (poly_deg complex_ring p) p = poly_0 complex_ring)
`;;

let distinct_minpolys_total_deg = `
  !P.
  FINITE P ==>
  distinct_minpolys P ==>
  (P = {}
   <=> nsum P (\p. poly_deg complex_ring p) = 0)
`;;

let distinct_minpolys_monic_vanishing_at_simple = `
  !p.
  ring_polynomial QinC_ring p ==>
  monic QinC_ring p ==>
  ring_irreducible(x_poly QinC_ring) p ==>
  monic_vanishing_at complex_ring (complex_root p) I = p
`;;

let distinct_minpolys_monic_vanishing_at = `
  !P p.
  distinct_minpolys P ==>
  p IN P ==>
  monic_vanishing_at complex_ring (complex_root p) I = p
`;;

let distinct_minpolys_deg_nonzero = `
  !P p.
  distinct_minpolys P ==>
  p IN P ==>
  ~(poly_deg complex_ring p = 0)
`;;

let distinct_minpolys_finite_root_simple = `
  !p.
  ring_polynomial QinC_ring p ==>
  monic QinC_ring p ==>
  ring_irreducible(x_poly QinC_ring) p ==>
  FINITE(complex_root p)
`;;

let distinct_minpolys_finite_root = `
  !P p.
  distinct_minpolys P ==>
  p IN P ==>
  FINITE(complex_root p)
`;;

let distinct_minpolys_card_root = `
  !P p.
  distinct_minpolys P ==>
  p IN P ==>
  CARD(complex_root p) = poly_deg complex_ring p
`;;

let distinct_minpolys_denominator = `
  !P.
  FINITE P ==>
  distinct_minpolys P ==>
  ?D. D IN ZinC /\
      ~(D = Cx(&0)) /\
      (!p. p IN P ==>
           !i. D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC
      )
`;;

let weighted_powersums_distinct_minpolys = `
  !P D B n.
  FINITE P ==>
  distinct_minpolys P ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  D pow n *
  (ring_sum complex_ring P
     (\p. (complex_of_int(B p)) * complex_root_powersums p n))
  IN ZinC
`;;

let distinct_minpolys_distinct_roots = `
  !P p q z.
  distinct_minpolys P ==>
  p IN P ==>
  q IN P ==>
  ~(p = q) ==>
  complex_root p z ==>
  ~(complex_root q z)
`;;

let distinct_minpolys_zero_root = `
  !P q.
  distinct_minpolys P ==>
  q IN P ==>
  complex_root q (Cx(&0)) ==>
  q = x_pow QinC_ring 1
`;;

let monic_factorization_distinct_minpolys = `
  !f.
  ring_polynomial QinC_ring f ==>
  monic QinC_ring f ==>
  ?P e. (
    FINITE P /\
    distinct_minpolys P /\
    (!p. p IN P ==> ~(e p = 0)) /\
    poly_product QinC_ring P (\p. poly_pow QinC_ring p (e p)) = f
  )
`;;

let multi_monic_factorization_distinct_minpolys = `
  !S f.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial QinC_ring (f s)) ==>
  (!s:X. s IN S ==> monic QinC_ring (f s)) ==>
  ?P e. (
    FINITE P /\
    distinct_minpolys P /\
    (!s. s IN S ==>
         poly_product QinC_ring P (\p. poly_pow QinC_ring p (e s p)) = f s
    )
  )
`;;

(* ===== more on binomial coefficients *)

let binom_coeff = `
  !n d.
  coeff d (
    poly_pow integer_ring (
      poly_add integer_ring
        (x_pow integer_ring 0)
        (x_pow integer_ring 1)
    ) n
  )
  = &(binom(n,d)):int
`;;

let binom_sum = `
  !m n d.
  binom(m+n,d) = nsum(0..d) (\i. binom(m,i) * binom(n,d-i))
`;;

let binom_rowsum = `
  !m.
  nsum(0..m) (\i. binom(m,i)) = 2 EXP m
`;;

let binom_rowsum_partial = `
  !m k.
  nsum(0..k) (\i. binom(m,i)) <= 2 EXP m
`;;

(* ===== bounds on (reversed) coefficients in terms of roots *)

let coeff_root_bound_1 = `
  !A:real d.
  norm(coeff d (poly_1 complex_ring))
  <= A pow d * &(binom(0,d))
`;;

let coeff_root_bound_one_minus_constx = `
  !c:complex A:real d:num.
  norm(c) <= A ==>
  norm(coeff d (one_minus_constx complex_ring c))
  <= A pow d * &(binom(1,d))
`;;

let coeff_root_bound_mul = `
  !p q (A:real) m n.
  (!d. norm(coeff d p) <= A pow d * &(binom(m,d))) ==>
  (!d. norm(coeff d q) <= A pow d * &(binom(n,d))) ==>
  (!d. norm(coeff d (poly_mul complex_ring p q)) <= A pow d * &(binom(m+n,d)))
`;;

let coeff_root_bound_product = `
  !p (A:real) m S.
  FINITE S ==>
  (!s:X d. s IN S ==> norm(coeff d (p s)) <= A pow d * &(binom(m s,d))) ==>
  (!d. norm(coeff d (poly_product complex_ring S p)) <= A pow d * &(binom(nsum S m,d)))
`;;

(* or can prove this via coeff_root_bound_product *)
let coeff_root_bound_pow = `
  !p (A:real) m n.
  ring_powerseries complex_ring p ==>
  (!d. norm(coeff d p) <= A pow d * &(binom(m,d))) ==>
  (!d. norm(coeff d (poly_pow complex_ring p n)) <= A pow d * &(binom(m*n,d)))
`;;

(* ===== first-order Stirling lower bound *)

let factorial_lower_bound = `
  !n.
  (&n / exp(&1)) pow n <= &(FACT n)
`;;

(* ===== poly_ord p z: order of vanishing of polynomial p at z *)

let poly_ord = new_definition `
  poly_ord (p:(1->num)->complex) (z:complex)
  = @e:num. (
      ?q:(1->num)->complex. (
        ring_polynomial complex_ring q /\
        ~(complex_root q z) /\
        p = poly_mul complex_ring (
          poly_pow complex_ring (
            x_minus_const complex_ring z
          ) e
        ) (
          q
        )
      )
    )
`;;

let poly_ord_exists_lemma = `
  !n p:(1->num)->complex.
  ring_polynomial complex_ring p ==>
  ~(p = poly_0 complex_ring) ==>
  poly_deg complex_ring p = n ==>
  ?e:num q:(1->num)->complex. (
    ring_polynomial complex_ring q /\
    ~(complex_root q z) /\
    p = poly_mul complex_ring (
      poly_pow complex_ring (
        x_minus_const complex_ring z
      ) e
    ) (
      q
    )
  )
`;;

let poly_ord_exists_lemma2 = `
  !p:(1->num)->complex.
  ring_polynomial complex_ring p ==>
  ~(p = poly_0 complex_ring) ==>
  ?e q:(1->num)->complex. (
    ring_polynomial complex_ring q /\
    ~(complex_root q z) /\
    p = poly_mul complex_ring (
      poly_pow complex_ring (
        x_minus_const complex_ring z
      ) e
    ) (
      q
    )
  )
`;;

let poly_ord_exists = `
  !p:(1->num)->complex.
  ring_polynomial complex_ring p ==>
  ~(p = poly_0 complex_ring) ==>
  ?q:(1->num)->complex. (
    ring_polynomial complex_ring q /\
    ~(complex_root q z) /\
    p = poly_mul complex_ring (
      poly_pow complex_ring (
        x_minus_const complex_ring z
      ) (poly_ord p z)
    ) (
      q
    )
  )
`;;

let poly_ord_unique = `
  !p:(1->num)->complex q e.
  ring_polynomial complex_ring q ==>
  ~(complex_root q z) ==>
  p = poly_mul complex_ring (
    poly_pow complex_ring (
      x_minus_const complex_ring z
    ) e
  ) (
    q
  ) ==>
  ( ring_polynomial complex_ring p /\
    ~(p = poly_0 complex_ring) /\
    e = poly_ord p z
  )
`;;

let poly_ord_unique_0 = `
  !p:(1->num)->complex z.
  ring_polynomial complex_ring p ==>
  ~(complex_root p z) ==>
  ( ~(p = poly_0 complex_ring) /\
    poly_ord p z = 0
  )
`;;

let poly_ord_unique_1 = `
  !p:(1->num)->complex q z.
  ring_polynomial complex_ring q ==>
  ~(complex_root q z) ==>
  p = poly_mul complex_ring (
    x_minus_const complex_ring z
  ) (
    q
  ) ==>
  ( ring_polynomial complex_ring p /\
    ~(p = poly_0 complex_ring) /\
    poly_ord p z = 1
  )
`;;

let poly_ord_const = `
  !c z.
  ~(c = Cx(&0)) ==>
  (
    ring_polynomial complex_ring (poly_const complex_ring c:(1->num)->complex) /\
    ~(poly_const complex_ring c = poly_0 complex_ring:(1->num)->complex) /\
    poly_ord(poly_const complex_ring c) z = 0
  )
`;;

let poly_ord_1 = `
  !z.
  ring_polynomial complex_ring (poly_1 complex_ring:(1->num)->complex) /\
  ~(poly_1 complex_ring = poly_0 complex_ring:(1->num)->complex) /\
  poly_ord(poly_1 complex_ring) z = 0
`;;

let poly_ord_x_minus_const = `
  !c z.
  ring_polynomial complex_ring (x_minus_const complex_ring c) /\
  ~(x_minus_const complex_ring c = poly_0 complex_ring) /\
  poly_ord (x_minus_const complex_ring c) z
  = if z = c then 1 else 0
`;;

let poly_ord_mul = `
  !p:(1->num)->complex q z.
  ring_polynomial complex_ring p ==>
  ring_polynomial complex_ring q ==>
  ~(p = poly_0 complex_ring) ==>
  ~(q = poly_0 complex_ring) ==>
  (
    ring_polynomial complex_ring (poly_mul complex_ring p q) /\
    ~(poly_mul complex_ring p q = poly_0 complex_ring) /\
    poly_ord (poly_mul complex_ring p q) z
    = poly_ord p z + poly_ord q z
  )
`;;

let poly_ord_product = `
  !p z S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial complex_ring (p s)) ==>
  (!s:X. s IN S ==> ~(p s = poly_0 complex_ring)) ==>
  (
    ring_polynomial complex_ring (poly_product complex_ring S p) /\
    ~(poly_product complex_ring S p = poly_0 complex_ring) /\
    poly_ord (poly_product complex_ring S p) z
    = nsum S (\s. poly_ord (p s) z)
  )
`;;

let poly_ord_monic_vanishing_at = `
  !S c z.
  FINITE S ==>
  (
    ring_polynomial complex_ring (monic_vanishing_at complex_ring S c) /\
    ~(monic_vanishing_at complex_ring S c = poly_0 complex_ring) /\
    poly_ord (monic_vanishing_at complex_ring S c) z
    = CARD {s:X | s IN S /\ z = c s}
  )
`;;

let poly_ord_monic_vanishing_at_numpreimages = `
  !S:X->bool c z.
  FINITE S ==>
  (
    ring_polynomial complex_ring (monic_vanishing_at complex_ring S c) /\
    ~(monic_vanishing_at complex_ring S c = poly_0 complex_ring) /\
    poly_ord (monic_vanishing_at complex_ring S c) z =
    numpreimages c S z
  )
`;;

let poly_ord_one_minus_constx = `
  !c z.
  ring_polynomial complex_ring (one_minus_constx complex_ring c) /\
  ~(one_minus_constx complex_ring c = poly_0 complex_ring) /\
  poly_ord (one_minus_constx complex_ring c) z
  = if c * z = Cx(&1) then 1 else 0
`;;

let poly_ord_pow = `
  !p:(1->num)->complex n z.
  ring_polynomial complex_ring p ==>
  ~(p = poly_0 complex_ring) ==>
  (
    ring_polynomial complex_ring (poly_pow complex_ring p n) /\
    ~(poly_pow complex_ring p n = poly_0 complex_ring) /\
    poly_ord (poly_pow complex_ring p n) z
    = n * poly_ord p z
  )
`;;

(* strict special case of poly_ord_x_pow *)
let poly_ord_x_pow_1 = `
  !z.
  ring_polynomial complex_ring (x_pow complex_ring 1) /\
  ~(x_pow complex_ring 1 = poly_0 complex_ring) /\
  poly_ord (x_pow complex_ring 1) z
  = if z = Cx(&0) then 1 else 0
`;;

let poly_ord_x_pow = `
  !n z.
  ring_polynomial complex_ring (x_pow complex_ring n) /\
  ~(x_pow complex_ring n = poly_0 complex_ring) /\
  poly_ord (x_pow complex_ring n) z
  = if z = Cx(&0) then n else 0
`;;

let poly_ord_mul_0 = `
  !p:(1->num)->complex q z.
  ( ring_polynomial complex_ring p /\
    ~(p = poly_0 complex_ring) /\
    poly_ord p z = 0
  ) ==>
  ( ring_polynomial complex_ring q /\
    ~(q = poly_0 complex_ring) /\
    poly_ord q z = 0
  ) ==>
  (
    ring_polynomial complex_ring (poly_mul complex_ring p q) /\
    ~(poly_mul complex_ring p q = poly_0 complex_ring) /\
    poly_ord (poly_mul complex_ring p q) z = 0
  )
`;;

let poly_ord_ge_if = `
  !p:(1->num)->complex f n.
  ring_polynomial complex_ring f ==>
  p = poly_mul complex_ring (poly_pow complex_ring (x_minus_const complex_ring z) n) f ==>
  (p = poly_0 complex_ring \/ n <= poly_ord p z)
`;;

let poly_ord_ge = `
  !p:(1->num)->complex n.
  ring_polynomial complex_ring p ==>
  ((p = poly_0 complex_ring \/ n <= poly_ord p z)
   <=> ?f:(1->num)->complex. (
         ring_polynomial complex_ring f /\
         p = poly_mul complex_ring (poly_pow complex_ring (x_minus_const complex_ring z) n) f
       )
  )
`;;

let poly_ord_mul_ge_ge = `
  !p:(1->num)->complex q z m n.
  ring_polynomial complex_ring p ==>
  ( p = poly_0 complex_ring \/
    m <= poly_ord p z
  ) ==>
  ring_polynomial complex_ring q ==>
  ( q = poly_0 complex_ring \/
    n <= poly_ord q z
  ) ==>
  ( ring_polynomial complex_ring (poly_mul complex_ring p q) /\
    ( poly_mul complex_ring p q = poly_0 complex_ring \/
      m + n <= poly_ord (poly_mul complex_ring p q) z
    )
  )
`;;

let poly_ord_mul_ge_ge0 = `
  !p:(1->num)->complex q z n.
  ring_polynomial complex_ring p ==>
  ( p = poly_0 complex_ring \/
    n <= poly_ord p z
  ) ==>
  ring_polynomial complex_ring q ==>
  ( ring_polynomial complex_ring (poly_mul complex_ring p q) /\
    ( poly_mul complex_ring p q = poly_0 complex_ring \/
      n <= poly_ord (poly_mul complex_ring p q) z
    )
  )
`;;

let poly_ord_mul_ge0_ge = `
  !p:(1->num)->complex q z n.
  ring_polynomial complex_ring p ==>
  ring_polynomial complex_ring q ==>
  ( q = poly_0 complex_ring \/
    n <= poly_ord q z
  ) ==>
  ( ring_polynomial complex_ring (poly_mul complex_ring p q) /\
    ( poly_mul complex_ring p q = poly_0 complex_ring \/
      n <= poly_ord (poly_mul complex_ring p q) z
    )
  )
`;;

let poly_ord_neg_ge = `
  !p:(1->num)->complex z n.
  ring_polynomial complex_ring p ==>
  (p = poly_0 complex_ring \/ n <= poly_ord p z) ==>
  (poly_neg complex_ring p = poly_0 complex_ring \/ n <= poly_ord(poly_neg complex_ring p) z)
`;;

let poly_ord_add_ge = `
  !p:(1->num)->complex q z n.
  ring_polynomial complex_ring p ==>
  ring_polynomial complex_ring q ==>
  (p = poly_0 complex_ring \/ n <= poly_ord p z) ==>
  (q = poly_0 complex_ring \/ n <= poly_ord q z) ==>
  (poly_add complex_ring p q = poly_0 complex_ring \/ n <= poly_ord(poly_add complex_ring p q) z)
`;;

let poly_ord_sum_ge = `
  !p z n S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial complex_ring (p s)) ==>
  (!s:X. s IN S ==> (p s = poly_0 complex_ring \/ n <= poly_ord (p s) z)) ==>
  (poly_sum complex_ring S p = poly_0 complex_ring \/ n <= poly_ord(poly_sum complex_ring S p) z)
`;;

let poly_ord_sub_ge = `
  !p:(1->num)->complex q z n.
  ring_polynomial complex_ring p ==>
  ring_polynomial complex_ring q ==>
  (p = poly_0 complex_ring \/ n <= poly_ord p z) ==>
  (q = poly_0 complex_ring \/ n <= poly_ord q z) ==>
  (poly_sub complex_ring p q = poly_0 complex_ring \/ n <= poly_ord(poly_sub complex_ring p q) z)
`;;

let poly_ord_add_dominant = `
  !p:(1->num)->complex q z n.
  ring_polynomial complex_ring p ==>
  ring_polynomial complex_ring q ==>
  (p = poly_0 complex_ring \/ n <= poly_ord p z) ==>
  ~(q = poly_0 complex_ring) ==>
  poly_ord q z < n ==>
  ( ~(poly_add complex_ring p q = poly_0 complex_ring) /\
    poly_ord(poly_add complex_ring p q) z = poly_ord q z
  )
`;;

let poly_ord_sub_dominant = `
  !p:(1->num)->complex q z n.
  ring_polynomial complex_ring p ==>
  ring_polynomial complex_ring q ==>
  (p = poly_0 complex_ring \/ n <= poly_ord p z) ==>
  ~(q = poly_0 complex_ring) ==>
  poly_ord q z < n ==>
  ( ~(poly_sub complex_ring p q = poly_0 complex_ring) /\
    poly_ord(poly_sub complex_ring p q) z = poly_ord q z
  )
`;;

let poly_ord_sum_dominant = `
  !p z n S t.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial complex_ring (p s)) ==>
  (!s:X. s IN S ==> ~(s = t) ==> (p s = poly_0 complex_ring) \/ n <= poly_ord (p s) z) ==>
  t IN S ==>
  ~(p t = poly_0 complex_ring) ==>
  poly_ord (p t) z < n ==>
  ( ring_polynomial complex_ring (poly_sum complex_ring S p) /\
    ~(poly_sum complex_ring S p = poly_0 complex_ring) /\
    poly_ord(poly_sum complex_ring S p) z = poly_ord (p t) z
  )
`;;

(* order of derivative of p/q when p/q has no pole at z *)
let poly_ord_derivative_ge = `
  !p:(1->num)->complex q PqpQ z.
  ring_polynomial complex_ring q ==>
  ring_polynomial complex_ring p ==>
  ~(q = poly_0 complex_ring) ==>
  (p = poly_0 complex_ring \/ poly_ord q z <= poly_ord p z) ==>
  PqpQ =
    poly_sub complex_ring (
      poly_mul complex_ring (
        x_derivative complex_ring p
      ) (
        q
      )
    ) (
      poly_mul complex_ring (
        p
      ) (
        x_derivative complex_ring q
      )
    )
  ==> (
    PqpQ = poly_0 complex_ring \/
    2 * poly_ord q z <= poly_ord PqpQ z
  )
`;;

let poly_ord_derivative_pole_lemma = `
  !z:complex m n.
  poly_sub complex_ring (
    poly_mul complex_ring (
      x_derivative complex_ring (
        poly_pow complex_ring (
          x_minus_const complex_ring z
        ) m
      )
    ) (
      poly_pow complex_ring (
        x_minus_const complex_ring z
      ) n
    )
  ) (
    poly_mul complex_ring (
      poly_pow complex_ring (
        x_minus_const complex_ring z
      ) m
    ) (
      x_derivative complex_ring (
        poly_pow complex_ring (
          x_minus_const complex_ring z
        ) n
      )
    )
  )
  =
  poly_mul complex_ring (
    poly_sub complex_ring (
      poly_const complex_ring (ring_of_num complex_ring m)
    ) (
      poly_const complex_ring (ring_of_num complex_ring n)
    )
  ) (
    poly_pow complex_ring (
      x_minus_const complex_ring z
    ) ((m+n)-1)
  )
`;;

(* order of derivative of p/q when p/q has a pole at z *)
let poly_ord_derivative_pole = `
  !p:(1->num)->complex q PqpQ z.
  ring_polynomial complex_ring q ==>
  ring_polynomial complex_ring p ==>
  ~(q = poly_0 complex_ring) ==>
  ~(p = poly_0 complex_ring) ==>
  poly_ord p z < poly_ord q z ==>
  PqpQ =
    poly_sub complex_ring (
      poly_mul complex_ring (
        x_derivative complex_ring p
      ) (
        q
      )
    ) (
      poly_mul complex_ring (
        p
      ) (
        x_derivative complex_ring q
      )
    )
  ==> (
    ring_polynomial complex_ring PqpQ /\
    ~(PqpQ = poly_0 complex_ring) /\
    poly_ord PqpQ z = (poly_ord p z + poly_ord q z) - 1
  )
`;;

let ord_minpoly = `
  !P q y.
  FINITE P ==>
  distinct_minpolys P ==>
  q IN P ==>
  poly_ord q y = (if complex_root q y then 1 else 0)
`;;

let ord_pow_minpoly = `
  !P q y n.
  FINITE P ==>
  distinct_minpolys P ==>
  q IN P ==>
  poly_ord (poly_pow QinC_ring q n) y
  = (if complex_root q y then n else 0)
`;;

let ord_product_distinct_minpolys = `
  !P e z.
  FINITE P ==>
  distinct_minpolys P ==>
  poly_ord (poly_product QinC_ring P (\p. poly_pow QinC_ring p (e p))) z
  = nsum P (\p. if complex_root p z then e p else 0)
`;;

let ord_product_distinct_minpolys_root = `
  !P q e z.
  FINITE P ==>
  distinct_minpolys P ==>
  q IN P ==>
  complex_root q z ==>
  poly_ord (poly_product QinC_ring P (\p. poly_pow QinC_ring p (e p))) z
  = e q
`;;

let sum_root_decomposition_if_monic_vanishing_at_factorization_lemma = `
  !P:((1->num)->complex)->bool S:X->bool e:((1->num)->complex)->num c:X->complex g:complex->complex.
  FINITE P ==>
  distinct_minpolys P ==>
  FINITE S ==>
  (!p. p IN P ==> ~(e p = 0)) ==>
  poly_product QinC_ring P (\p. poly_pow QinC_ring p (e p))
  = monic_vanishing_at complex_ring S c ==>
  ring_sum complex_ring P (\p. Cx (&(e p)) * ring_sum complex_ring (complex_root p) g) =
  ring_sum complex_ring S (g o c)
`;;

let sum_root_decomposition_if_monic_vanishing_at_factorization = `
  !P:((1->num)->complex)->bool S:X->bool e:((1->num)->complex)->num c:X->complex g:complex->complex.
  FINITE P ==>
  distinct_minpolys P ==>
  FINITE S ==>
  poly_product QinC_ring P (\p. poly_pow QinC_ring p (e p))
  = monic_vanishing_at complex_ring S c ==>
  ring_sum complex_ring P (\p. Cx (&(e p)) * ring_sum complex_ring (complex_root p) g) =
  ring_sum complex_ring S (g o c)
`;;

(* ===== core transcendence arguments *)

let transcendence_v_denom = `
  !P D B u.
  FINITE P ==>
  distinct_minpolys P ==>
  D IN ZinC ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  !n vn.
  vn = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i) ==>
  D pow n * vn IN ZinC
`;;

(* could do transcendence_v_denom by specializing to k = 0 *)
let transcendence_w_denom = `
  !P D B u.
  FINITE P ==>
  distinct_minpolys P ==>
  D IN ZinC ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  !n k wn.
  wn = (if k <= n then ring_sum complex_ring (0..n-k) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i) else Cx(&0)) ==>
  (D pow (n-k) * wn) / Cx(&(FACT k)) IN ZinC
`;;

let transcendence_H_poly = `
  !P H t.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  ring_polynomial complex_ring H
`;;

let transcendence_Gp_poly = `
  !P p.
  FINITE P ==>
  distinct_minpolys P ==>
  p IN P ==>
  ring_polynomial complex_ring (poly_product complex_ring (P DELETE p) (\q. x_truncreverse QinC_ring (poly_deg complex_ring q) q))
`;;

let transcendence_H_product = `
  !P H t.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  H = poly_product QinC_ring P (\p. x_truncreverse QinC_ring (poly_deg complex_ring p) p)
`;;

let transcendence_H_product_complex_ring = `
  !P H t.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  H = poly_product complex_ring P (\p. x_truncreverse QinC_ring (poly_deg complex_ring p) p)
`;;

let transcendence_H_botcoeff1 = `
  !P H t.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  coeff 0 H = Cx(&1)
`;;

let transcendence_H_denom = `
  !P H D t.
  FINITE P ==>
  distinct_minpolys P ==>
  D IN ZinC ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!i. D pow i * coeff i H IN ZinC)
`;;

let transcendence_H_pow_denom = `
  !P H D t k.
  FINITE P ==>
  distinct_minpolys P ==>
  D IN ZinC ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!i. D pow i * coeff i (poly_pow QinC_ring H k) IN ZinC)
`;;

let transcendence_newton_pe = `
  !P p e.
  FINITE P ==>
  distinct_minpolys P ==>
  p IN P ==>
  poly_mul complex_ring (
    poly_pow complex_ring (
      x_truncreverse complex_ring (poly_deg complex_ring p) p
    ) (e + 1)
  ) (
    poly_sum complex_ring (complex_root p) (\s.
      series_from_coeffs (\n.
        ring_mul complex_ring (
          Cx(&(FACT e * binom (n,e)))
        ) (
          ring_pow complex_ring s (n - e)
        )
      )
    )
  )
  = scaled_pow_newton_rightside complex_ring I (complex_root p) e
`;;

let transcendence_newton_He_Ge = `
  !P t H.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  !p Gp.
  p IN P ==>
  Gp = poly_product complex_ring (P DELETE p) (\p. x_truncreverse QinC_ring (poly_deg complex_ring p) p) ==>
  !e.
  poly_mul complex_ring (
    poly_pow complex_ring H (e+1)
  ) (
    poly_sum complex_ring (complex_root p) (\s.
      series_from_coeffs (\n.
        ring_mul complex_ring (
          Cx(&(FACT e * binom (n,e)))
        ) (
          ring_pow complex_ring s (n - e)
        )
      )
    )
  )
  =
  poly_mul complex_ring (
    poly_pow complex_ring Gp (e+1)
  ) (
    scaled_pow_newton_rightside complex_ring I (complex_root p) e
  )
`;;

let transcendence_newton_Hk = `
  !P t H p Gp e k.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  p IN P ==>
  Gp = poly_product complex_ring (P DELETE p) (\p. x_truncreverse QinC_ring (poly_deg complex_ring p) p) ==>
  e < k ==>
  poly_mul complex_ring (
    poly_pow complex_ring H k
  ) (
    poly_sum complex_ring (complex_root p) (\s.
      series_from_coeffs (\n.
        ring_mul complex_ring (
          Cx(&(FACT e * binom (n,e)))
        ) (
          ring_pow complex_ring s (n - e)
        )
      )
    )
  )
  =
  poly_mul complex_ring (
    poly_pow complex_ring H (k-(e+1))
  ) (
    poly_mul complex_ring (
      poly_pow complex_ring Gp (e+1)
    ) (
      scaled_pow_newton_rightside complex_ring I (complex_root p) e
    )
  )
`;;

let transcendence_newton_Hk_psum = `
  !P B t H G u e k.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!p. p IN P ==> G p = poly_product complex_ring (P DELETE p) (\q. x_truncreverse QinC_ring (poly_deg complex_ring q) q)) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  e < k ==>
  poly_mul complex_ring (
    poly_pow complex_ring H k
  ) (
    series_from_coeffs (\n.
      Cx(&(FACT(e) * binom(n,e))) * u(n-e)
    )
  )
  =
  poly_sum complex_ring P (\p:(1->num)->complex.
    poly_mul complex_ring (
      poly_const complex_ring ((complex_of_int(B p)))
    ) (
      poly_mul complex_ring (
        poly_pow complex_ring H (k-(e+1))
      ) (
        poly_mul complex_ring (
          poly_pow complex_ring (G p) (e+1)
        ) (
          scaled_pow_newton_rightside complex_ring I (complex_root p) e
        )
      )
    )
  )
`;;

let transcendence_Huv_lemma = `
  !H u k.
  poly_mul complex_ring (
    poly_pow complex_ring H k
  ) (
    series_from_coeffs (\n.
      ring_sum complex_ring {e | e < k} (\e.
        Cx(&(FACT(e) * binom(n,e))) * u(n-e)
      )
    )
  )
  =
  poly_sum complex_ring {e | e < k} (\e:num.
    poly_mul complex_ring (
      poly_pow complex_ring H k
    ) (
      series_from_coeffs (\n.
        Cx(&(FACT e * binom (n,e))) * u(n-e))
    )
  )
`;;

let transcendence_H_main = `
  !P B t H G u k.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!p. p IN P ==> G p = poly_product complex_ring (P DELETE p) (\p. x_truncreverse QinC_ring (poly_deg complex_ring p) p)) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  poly_mul complex_ring (
    poly_pow complex_ring H k
  ) (
    series_from_coeffs (\n.
      ring_sum complex_ring {e | e < k} (\e.
        Cx(&(FACT(e) * binom(n,e))) * u(n-e)
      )
    )
  )
  = poly_sum complex_ring {e | e < k} (\e:num.
      poly_sum complex_ring P (\p:(1->num)->complex.
        poly_mul complex_ring (
          poly_const complex_ring ((complex_of_int(B p)))
        ) (
          poly_mul complex_ring (
            poly_pow complex_ring H (k-(e+1))
          ) (
            poly_mul complex_ring (
              poly_pow complex_ring (G p) (e+1)
            ) (
              scaled_pow_newton_rightside complex_ring I (complex_root p) e
            )
          )
        )
      )
    )
`;;

let transcendence_Htimes_poly = `
  !P B t H u k.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  ring_polynomial complex_ring (
    poly_mul complex_ring (
      poly_pow complex_ring H k
    ) (
      series_from_coeffs (\n.
        ring_sum complex_ring {e | e < k} (\e.
          Cx(&(FACT(e) * binom(n,e))) * u(n-e)
        )
      )
    )
  )
`;;

let transcendence_H_deg_G_lemma = `
  !p d g s t n:num.
  ~(p = 0) ==>
  d <= g + s ==>
  g <= (e+1)*n ==>
  s <= e + (p-1)*(e+1) ==>
  t = p+n ==>
  d <= e+(t-1)*(e+1)
`;;

let transcendence_H_deg_G = `
  !P t p Gp e.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  p IN P ==>
  Gp = poly_product complex_ring (P DELETE p) (\q. x_truncreverse QinC_ring (poly_deg complex_ring q) q) ==>
  poly_deg complex_ring (
    poly_mul complex_ring (
      poly_pow complex_ring Gp (e + 1)
    ) (
      scaled_pow_newton_rightside complex_ring I (complex_root p) e
    )
  ) <= e + (t-1)*(e+1)
`;;

let transcendence_H_deg_HG = `
  !P t p Gp e k.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  p IN P ==>
  Gp = poly_product complex_ring (P DELETE p) (\q. x_truncreverse QinC_ring (poly_deg complex_ring q) q) ==>
  e < k ==>
  poly_deg complex_ring (
    poly_mul complex_ring (
      poly_pow complex_ring H (k - (e + 1))
    ) (
      poly_mul complex_ring (
        poly_pow complex_ring Gp (e + 1)
      ) (
        scaled_pow_newton_rightside complex_ring I (complex_root p) e
      )
    )
  ) <= e + (t-1)*(e+1) + t*(k-(e+1))
`;;

let transcendence_H_deg_HG_simpler = `
  !P t p Gp e k.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  p IN P ==>
  Gp = poly_product complex_ring (P DELETE p) (\q. x_truncreverse QinC_ring (poly_deg complex_ring q) q) ==>
  e < k ==>
  poly_deg complex_ring (
    poly_mul complex_ring (
      poly_pow complex_ring H (k - (e + 1))
    ) (
      poly_mul complex_ring (
        poly_pow complex_ring Gp (e + 1)
      ) (
        scaled_pow_newton_rightside complex_ring I (complex_root p) e
      )
    )
  ) <= t*k-1
`;;

let transcendence_H_deg_overall = `
  !P B t H u k.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  poly_deg complex_ring (
    poly_mul complex_ring (
      poly_pow complex_ring H k
    ) (
      series_from_coeffs (\n.
        ring_sum complex_ring {e | e < k} (\e.
          Cx(&(FACT(e) * binom(n,e))) * u(n-e)
        )
      )
    )
  ) <= t*k-1
`;;

let transcendence_vw_diff = `
  !u n k vn wn.
  vn = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i) ==>
  wn = (if k <= n then ring_sum complex_ring (0..n-k) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i) else Cx(&0)) ==>
  vn - wn = ring_sum complex_ring {e | e < k} (\e. Cx(&(FACT(e) * binom(n,e))) * u (n-e))
`;;

let transcendence_vw_diff_series = `
  !P B u v w.
  FINITE P ==>
  distinct_minpolys P ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  (!n. w n = if k <= n then ring_sum complex_ring (0..n-k) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i) else Cx(&0)) ==>
  poly_sub complex_ring (
    series_from_coeffs v
  ) (
    series_from_coeffs w
  ) =
  series_from_coeffs (\n.
    ring_sum complex_ring {e | e < k} (\e.
      Cx(&(FACT(e) * binom(n,e))) * u(n-e)
    )
  )
`;;

let transcendence_vw_diff_series_H = `
  !P B t H u v w k.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  (!n. w n = if k <= n then ring_sum complex_ring (0..n-k) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i) else Cx(&0)) ==>
  poly_sub complex_ring (
    poly_mul complex_ring (
      poly_pow complex_ring H k
    ) (
      series_from_coeffs v
    )
  ) (
    poly_mul complex_ring (
      poly_pow complex_ring H k
    ) (
    series_from_coeffs w
    )
  ) =
  poly_mul complex_ring (
    poly_pow complex_ring H k
  ) (
    series_from_coeffs (\n.
      ring_sum complex_ring {e | e < k} (\e.
        Cx(&(FACT(e) * binom(n,e))) * u(n-e)
      )
    )
  )
`;;

let transcendence_uv_trivial = `
  !P B u v.
  P = {} ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  (!n. u n = Cx(&0) /\ v n = Cx(&0))
`;;

let transcendence_vw_match = `
  !P B t H u v w.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  (!n k. k*t <= n ==>
         (!d. w d = if k <= d then ring_sum complex_ring (0..d-k) (\i. Cx(&(FACT(d-i) * binom(d,i))) * u i) else Cx(&0)) ==>
         coeff n (
           poly_mul complex_ring (
             poly_pow complex_ring H k
           ) (
             series_from_coeffs v
           )
         )
         =
         coeff n (
           poly_mul complex_ring (
             poly_pow complex_ring H k
           ) (
             series_from_coeffs w
           )
         )
  )
`;;

let transcendence_Hw_denom = `
  !P D B t H u w.
  FINITE P ==>
  distinct_minpolys P ==>
  D IN ZinC ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n k. k*t <= n ==>
         (!d. w d = if k <= d then ring_sum complex_ring (0..d-k) (\i. Cx(&(FACT(d-i) * binom(d,i))) * u i) else Cx(&0)) ==>
         (D pow (n-k) / Cx(&(FACT k))) *
         coeff n (
           poly_mul complex_ring (
             poly_pow complex_ring H k
           ) (
             series_from_coeffs w
           )
         ) IN ZinC
  )
`;;

let transcendence_Hv_denom = `
  !P D B t H u v.
  FINITE P ==>
  distinct_minpolys P ==>
  D IN ZinC ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  (!n k. k*t <= n ==>
         (D pow (n-k) / Cx(&(FACT k))) *
         coeff n (
           poly_mul complex_ring (
             poly_pow complex_ring H k
           ) (
             series_from_coeffs v
           )
         ) IN ZinC
  )
`;;

let transcendence_u_tail = `
  !P A B u.
  FINITE P ==>
  distinct_minpolys P ==>
  (!p z. p IN P ==> complex_root p z ==> norm z <= A) ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  !n.
  norm(vsum(0..n) (\i. u i / Cx(&(FACT i))))
  <= (sum P (\p:(1->num)->complex. abs (real_of_int (B p)) * &(poly_deg complex_ring p))) * exp A * A pow (n + 1) / &(FACT n)
`;;

let transcendence_v_bound = `
  !P A B u.
  FINITE P ==>
  distinct_minpolys P ==>
  (!p z. p IN P ==> complex_root p z ==> norm z <= A) ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  !n vn.
  vn = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i) ==>
  norm vn
  <= (sum P (\p:(1->num)->complex. abs (real_of_int (B p)) * &(poly_deg complex_ring p))) * exp A * A pow (n + 1)
`;;

let transcendence_p_bound = `
  !P p A.
  distinct_minpolys P ==>
  p IN P ==>
  (!z. complex_root p z ==> norm z <= A) ==>
  (!d. norm(coeff d (x_truncreverse QinC_ring (poly_deg complex_ring p) p)) <= A pow d * &(binom(poly_deg complex_ring p,d)))
`;;

let transcendence_H_bound = `
  !P A t H.
  FINITE P ==>
  distinct_minpolys P ==>
  (!p z. p IN P ==> complex_root p z ==> norm z <= A) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!d. norm(coeff d H) <= A pow d * &(binom(t,d)))
`;;

let transcendence_Hk_bound = `
  !P A t H k.
  FINITE P ==>
  distinct_minpolys P ==>
  (!p z. p IN P ==> complex_root p z ==> norm z <= A) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!d. norm(coeff d (poly_pow complex_ring H k)) <= A pow d * &(binom(k*t,d)))
`;;

let transcendence_A_nonnegative = `
  !P A.
  FINITE P ==>
  distinct_minpolys P ==>
  (!p z. p IN P ==> complex_root p z ==> norm z <= A) ==>
  (P = {} \/ &0 <= A)
`;;

let transcendence_Hv_bound = `
  !P A B t H u v.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  (!p z. p IN P ==> complex_root p z ==> norm z <= A) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  (!n k. norm (
           coeff n (
             poly_mul complex_ring (
               poly_pow complex_ring H k
             ) (
               series_from_coeffs v
             )
           )
         ) <= &2 pow (k*t) * sum P (\p. abs (real_of_int (B p)) * &(poly_deg complex_ring p)) * exp A * A pow (n + 1)
  )
`;;

let transcendence_Hv_zero = `
  !P A D B t H u v.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  (!p z. p IN P ==> complex_root p z ==> norm z <= A) ==>
  D IN ZinC ==>
  ~(D = Cx(&0)) ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  (!n k. k*t <= n ==>
         norm(D pow (n-k) / Cx(&(FACT k))) * &2 pow (k * t) * sum P (\p. abs (real_of_int (B p)) * &(poly_deg complex_ring p)) * exp A * A pow (n + 1) < &1 ==>
         coeff n (
           poly_mul complex_ring (
             poly_pow complex_ring H k
           ) (
             series_from_coeffs v
           )
         ) = Cx(&0)
  )
`;;

let transcendence_Hv_zero_Ptrivial = `
  !P H u v.
  P = {} ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  (!n k. coeff n (
           poly_mul complex_ring (
             poly_pow complex_ring H k
           ) (
             series_from_coeffs v
           )
         ) = Cx(&0)
  )
`;;

(* XXX: can improve bounds in proof *)
(* in particular: *)
(* first 10t is a proxy for 10t-1 *)
(* and 10t+1 is a proxy for 10t+1/k *)
(* and the first max(1,...) is a proxy for that^(1/k) *)
(* and 10 is a proxy for something like 1+1/k *)
let transcendence_Hv_zero_k0 = `
  !P A D B t H u v k0.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  (!p z. p IN P ==> complex_root p z ==> norm z <= A) ==>
  D IN ZinC ==>
  ~(D = Cx(&0)) ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  1 <= k0 ==>
  norm(D) pow (10*t) * &2 pow t * max (&1) (sum P (\p. abs (real_of_int (B p)) * &(poly_deg complex_ring p)) * exp A) * (max (&1) A) pow (10*t+1) * exp(&1) < &k0 ==>
  (!n k. k0 <= k ==>
         k*t <= n ==>
         n <= 10*k*t ==>
         coeff n (
           poly_mul complex_ring (
             poly_pow complex_ring H k
           ) (
             series_from_coeffs v
           )
         ) = Cx(&0)
  )
`;;

let transcendence_Hv_induction = `
  !P A D B t H u v k0.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  (!p z. p IN P ==> complex_root p z ==> norm z <= A) ==>
  D IN ZinC ==>
  ~(D = Cx(&0)) ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  1 <= k0 ==>
  norm(D) pow (10*t) * &2 pow t * max (&1) (sum P (\p. abs (real_of_int (B p)) * &(poly_deg complex_ring p)) * exp A) * (max (&1) A) pow (10*t+1) * exp(&1) < &k0 ==>
  (!j n k. k0 <= k ==>
           k*t <= n ==>
           n <= 10*k*t+j ==>
           coeff n (
             poly_mul complex_ring (
               poly_pow complex_ring H k
             ) (
               series_from_coeffs v
             )
           ) = Cx(&0)
  )
`;;

let transcendence_Hv_noupperbound = `
  !P A D B t H u v k0.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  (!p z. p IN P ==> complex_root p z ==> norm z <= A) ==>
  D IN ZinC ==>
  ~(D = Cx(&0)) ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  1 <= k0 ==>
  norm(D) pow (10*t) * &2 pow t * max (&1) (sum P (\p. abs (real_of_int (B p)) * &(poly_deg complex_ring p)) * exp A) * (max (&1) A) pow (10*t+1) * exp(&1) < &k0 ==>
  (!n k. k0 <= k ==>
         k*t <= n ==>
         coeff n (
           poly_mul complex_ring (
             poly_pow complex_ring H k
           ) (
             series_from_coeffs v
           )
         ) = Cx(&0)
  )
`;;

let transcendence_Hv_kexists = `
  !P A D B t H u v.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  (!p z. p IN P ==> complex_root p z ==> norm z <= A) ==>
  D IN ZinC ==>
  ~(D = Cx(&0)) ==>
  (!p i. p IN P ==> D pow i * (coeff (poly_deg complex_ring p - i) p) IN ZinC) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  ?k. 1 <= k /\
  !n. k*t <= n ==>
      coeff n (
        poly_mul complex_ring (
          poly_pow complex_ring H k
        ) (
          series_from_coeffs v
        )
      ) = Cx(&0)
`;;

(* could use sup in proof but sum seems a bit easier *)
let transcendence_Hv_kexists_v2 = `
  !P B t H u v.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  ?k. 1 <= k /\
  !n. k*t <= n ==>
      coeff n (
        poly_mul complex_ring (
          poly_pow complex_ring H k
        ) (
          series_from_coeffs v
        )
      ) = Cx(&0)
`;;

let transcendence_Hv_poly = `
  !P B t H u v.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  ?k. 1 <= k /\
  ring_polynomial complex_ring (
    poly_mul complex_ring (
      poly_pow complex_ring H k
    ) (
      series_from_coeffs v
    )
  )
`;;

let transcendence_uv_diffeq = `
  !u v.
  (!n. v n = ring_sum complex_ring (0..n) (\i. Cx(&(FACT(n-i) * binom(n,i))) * u i)) ==>
  poly_sub complex_ring (
    poly_sub complex_ring (
      series_from_coeffs v
    ) (
      poly_mul complex_ring (
        x_pow complex_ring 1
      ) (
        series_from_coeffs v
      )
    )
  ) (
    poly_mul complex_ring (
      x_pow complex_ring 2
    ) (
      x_derivative complex_ring (
        series_from_coeffs v
      )
    )
  ) = series_from_coeffs u
`;;

let ord_product_one_minus_constx_I = `
  !S y yinv.
  FINITE S ==>
  y * yinv = Cx(&1) ==>
  (
    ring_polynomial complex_ring (poly_product complex_ring S (\z. one_minus_constx complex_ring (I z))) /\
    ~(poly_product complex_ring S (\z. one_minus_constx complex_ring (I z)) = poly_0 complex_ring) /\
    poly_ord (poly_product complex_ring S (\z. one_minus_constx complex_ring (I z))) yinv
    = if y IN S then 1 else 0
  )
`;;

let ord_sum_product_one_minus_constx_I = `
  !S y yinv.
  FINITE S ==>
  y * yinv = Cx(&1) ==>
  y IN S ==>
  (
    ring_polynomial complex_ring (
      poly_sum complex_ring S (\t.
        poly_product complex_ring (S DELETE t) (\z.
          one_minus_constx complex_ring (I z)
        )
      )
    ) /\
    ~(
      poly_sum complex_ring S (\t.
        poly_product complex_ring (S DELETE t) (\z.
          one_minus_constx complex_ring (I z)
        )
      ) = poly_0 complex_ring
    ) /\
    poly_ord (
      poly_sum complex_ring S (\t.
        poly_product complex_ring (S DELETE t) (\z.
          one_minus_constx complex_ring (I z)
        )
      )
    ) yinv
    = 0
  )
`;;

let transcendence_ord_revp = `
  !P p y yinv.
  FINITE P ==>
  distinct_minpolys P ==>
  p IN P ==>
  y * yinv = Cx(&1) ==>
  (
    ring_polynomial complex_ring (x_truncreverse QinC_ring (poly_deg complex_ring p) p) /\
    ~(x_truncreverse QinC_ring (poly_deg complex_ring p) p = poly_0 complex_ring) /\
    poly_ord (x_truncreverse QinC_ring (poly_deg complex_ring p) p) yinv
    = if complex_root p y then 1 else 0
  )
`;;

let transcendence_ord_H = `
  !P t H.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!q y yinv.
    q IN P ==>
    complex_root q y ==>
    y * yinv = Cx(&1) ==>
    poly_ord H yinv = 1
  )
`;;

let transcendence_ord_Hk = `
  !P t H k.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!q y yinv.
    q IN P ==>
    complex_root q y ==>
    y * yinv = Cx(&1) ==>
    poly_ord (poly_pow complex_ring H k) yinv = k
  )
`;;

let transcendence_ord_Hu = `
  !P B t H u.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  (!q y yinv.
    q IN P ==>
    ~(B q = &0) ==>
    complex_root q y ==>
    y * yinv = Cx(&1) ==>
    (
      ring_polynomial complex_ring (poly_mul complex_ring H (series_from_coeffs u)) /\
      ~(poly_mul complex_ring H (series_from_coeffs u) = poly_0 complex_ring) /\
      poly_ord (poly_mul complex_ring H (series_from_coeffs u)) yinv = 0
    )
  )
`;;

let transcendence_ord_Hku = `
  !P B t H u k.
  FINITE P ==>
  distinct_minpolys P ==>
  t = nsum P (\p. poly_deg complex_ring p) ==>
  H = x_truncreverse QinC_ring t (poly_product QinC_ring P I) ==>
  (!n. u n = (ring_sum complex_ring P (\p. (complex_of_int(B p)) * complex_root_powersums p n))) ==>
  1 <= k ==>
  (!q y yinv.
    q IN P ==>
    ~(B q = &0) ==>
    complex_root q y ==>
    y * yinv = Cx(&1) ==>
    (
      ring_polynomial complex_ring (poly_mul complex_ring (poly_pow complex_ring H k) (series_from_coeffs u)) /\
      ~(poly_mul complex_ring (poly_pow complex_ring H k) (series_from_coeffs u) = poly_0 complex_ring) /\
      poly_ord (
        poly_mul complex_ring (
          poly_pow complex_ring H k
        ) (
          series_from_coeffs u
        )
      ) yinv = k-1
    )
  )
`;;

(*
if rational functions U = e/g and V = f/g
satisfy U = V - xV - x^2 V'
then U cannot have a pole of order 1 at any nonzero point
*)
let transcendence_pole_order_ne1 = `
  !U V e f g y yinv.
  y * yinv = Cx(&1) ==>
  ring_polynomial complex_ring e ==>
  ring_polynomial complex_ring f ==>
  ring_polynomial complex_ring g ==>
  ~(g = poly_0 complex_ring) ==>
  ~(e = poly_0 complex_ring) ==>
  poly_ord e yinv + 1 = poly_ord g yinv ==>
  poly_mul complex_ring g U = e ==>
  poly_mul complex_ring g V = f ==>
  poly_sub complex_ring (
    poly_sub complex_ring V (
      poly_mul complex_ring (x_pow complex_ring 1) V
    )
  ) (
    poly_mul complex_ring (x_pow complex_ring 2) (x_derivative complex_ring V)
  ) = U ==>
  F
`;;

let transcendence_mostly_0 = `
  !P B q y.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  q IN P ==>
  ~(B q = &0) ==>
  complex_root q y ==>
  y = Cx(&0)
`;;

let transcendence_mostly_0_x = `
  !P B q.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  q IN P ==>
  ~(B q = &0) ==>
  q = x_pow QinC_ring 1
`;;

let transcendence_all_0 = `
  !P B.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. complex_of_int(B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  (!q. q IN P ==> B q = &0)
`;;

let transcendence_all_0_ZinC = `
  !P B.
  FINITE P ==>
  distinct_minpolys P ==>
  (!p. p IN P ==> B p IN ZinC) ==>
  ring_sum complex_ring P (\p. (B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  (!p. p IN P ==> B p = Cx(&0))
`;;

let transcendence_all_0_QinC = `
  !P B.
  FINITE P ==>
  distinct_minpolys P ==>
  (!p. p IN P ==> B p IN QinC) ==>
  ring_sum complex_ring P (\p. (B p) * ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  (!p. p IN P ==> B p = Cx(&0))
`;;

let transcendence_all_0_QinC_weight1 = `
  !P.
  FINITE P ==>
  distinct_minpolys P ==>
  ring_sum complex_ring P (\p. ring_sum complex_ring (complex_root p) cexp) = Cx(&0) ==>
  P = {}
`;;

let transcendence_all_0_QinC_monic_vanishing_at = `
  !S c.
  FINITE S ==>
  ring_polynomial QinC_ring (monic_vanishing_at complex_ring S c) ==>
  ring_sum complex_ring S (\s:X. cexp(c s)) = Cx(&0) ==>
  S = {}
`;;

let transcendence_weighted_QinC_monic_vanishing_at = `
  !S:X->bool b:X->complex c:Y->complex f:X->(Y->bool).
  FINITE S ==>
  (!s. s IN S ==> b s IN QinC) ==>
  (!s. s IN S ==> FINITE(f s)) ==>
  (!s. s IN S ==> ring_polynomial QinC_ring (monic_vanishing_at complex_ring (f s) c)) ==>
  ring_sum complex_ring S (\s. b s * ring_sum complex_ring (f s) (cexp o c)) = Cx(&0) ==>
  (!a. ring_sum complex_ring S (\s. b s * Cx(&(numpreimages c (f s) a))) = Cx(&0))
`;;

(* ===== e is transcendental *)

(* warmup, marginally easier *)
let e_is_irrational = `
  ~(cexp(Cx(&1)) IN QinC)
`;;

let e_is_transcendental = `
  ~(algebraic_number(cexp(Cx(&1))))
`;;

(* ===== algebraic numbers closed under mul, add *)

let algebraic_number_mul = `
  !y z.
  algebraic_number y ==>
  algebraic_number z ==>
  algebraic_number (y*z)
`;;

(* or can prove this more directly on poly coeffs *)
let algebraic_number_neg = `
  !z.
  algebraic_number z ==>
  algebraic_number (-- z)
`;;

let algebraic_number_add = `
  !y z.
  algebraic_number y ==>
  algebraic_number z ==>
  algebraic_number (y+z)
`;;

let algebraic_number_subring = `
  algebraic_number subring_of complex_ring
`;;

let algebraic_number_sum = `
  !f S.
  FINITE S ==>
  (!s:X. s IN S ==> algebraic_number (f s)) ==>
  algebraic_number (ring_sum complex_ring S f)
`;;

(* ===== expformal c: the power series exp(cx) *)

let expformal = new_definition `
  expformal (c:complex)
  = series_from_coeffs (\n. c pow n / Cx(&(FACT n)))
`;;

let mul_expformal = `
  !u v.
  poly_mul complex_ring (expformal u) (expformal v)
  = expformal (u+v)
`;;

let expformal_0 = `
  expformal(Cx(&0)) = poly_1 complex_ring
`;;

let pow_expformal = `
  !u n.
  poly_pow complex_ring (expformal u) n
  = expformal (Cx(&n)*u)
`;;

let product_expformal = `
  !c S.
  FINITE S ==>
  poly_product complex_ring S (\s:X. expformal (c s))
  = expformal (ring_sum complex_ring S c)
`;;

let product_expformal_I = `
  !S.
  FINITE S ==>
  poly_product complex_ring S expformal
  = expformal (ring_sum complex_ring S I)
`;;

let expformal_powersums_QinC = `
  !S c:X->complex.
  FINITE S ==>
  (!n. ring_sum complex_ring S (\s:X. (c s) pow n) IN QinC) ==>
  ring_powerseries QinC_ring (poly_sum complex_ring S (\s:X. expformal (c s)))
`;;

let pow_expformal_powersums_QinC = `
  !S m.
  FINITE S ==>
  (!n. ring_sum complex_ring S (\z. z pow n) IN QinC) ==>
  ring_powerseries QinC_ring (
    poly_sum complex_ring S (\z.
      poly_pow complex_ring (expformal z) m
    )
  )
`;;

let carrier_QinC_series_subring_generated_refl = `
  ring_carrier(subring_generated
    (x_series complex_ring)
    (ring_carrier(x_series QinC_ring))
  )
  = ring_carrier(x_series QinC_ring)
`;;

let symfun_expformal_powersums_QinC = `
  !S m.
  FINITE S ==>
  (!n. ring_sum complex_ring S (\z. z pow n) IN QinC) ==>
  poly_sum complex_ring
    {U | U SUBSET S /\ CARD U = m}
    (\U. poly_product complex_ring U expformal)
  IN ring_carrier(x_series QinC_ring)
`;;

let symfun_expformal_powersums_QinC_v2 = `
  !S m.
  FINITE S ==>
  (!n. ring_sum complex_ring S (\z. z pow n) IN QinC) ==>
  poly_sum complex_ring
    {U | U SUBSET S /\ CARD U = m}
    (\U. expformal (ring_sum complex_ring U I))
  IN ring_carrier(x_series QinC_ring)
`;;

let symfun_expformal_powersums_QinC_v3 = `
  !S m d.
  FINITE S ==>
  (!n. ring_sum complex_ring S (\z. z pow n) IN QinC) ==>
  ring_sum complex_ring
    {U | U SUBSET S /\ CARD U = m}
    (\U. (ring_sum complex_ring U I) pow d)
  IN QinC
`;;

let resolvent_if_powersums_QinC = `
  !S m.
  FINITE S ==>
  (!n. ring_sum complex_ring S (\z. z pow n) IN QinC) ==>
  ring_polynomial QinC_ring (
    monic_vanishing_at complex_ring
      {U | U SUBSET S /\ CARD U = m}
      (\U. ring_sum complex_ring U I)
  )
`;;

(* can alternatively prove this via symmetric-function argument *)
let resolvent_if_poly_QinC = `
  !S m.
  FINITE S ==>
  ring_polynomial QinC_ring (
    monic_vanishing_at complex_ring S I
  ) ==>
  ring_polynomial QinC_ring (
    monic_vanishing_at complex_ring
      {U | U SUBSET S /\ CARD U = m}
      (\U. ring_sum complex_ring U I)
  )
`;;

let prod_resolvent_if_poly_QinC_lemma = `
  !S.
  FINITE S ==>
  monic_vanishing_at complex_ring
    {U | U SUBSET S}
    (\U. ring_sum complex_ring U I)
  =
  poly_product complex_ring (0..CARD S) (\m.
    monic_vanishing_at complex_ring
      {U | U SUBSET S /\ CARD U = m}
      (\U. ring_sum complex_ring U I)
  )
`;;

let prod_resolvent_if_poly_QinC = `
  !S.
  FINITE S ==>
  ring_polynomial QinC_ring (
    monic_vanishing_at complex_ring S I
  ) ==>
  ring_polynomial QinC_ring (
    monic_vanishing_at complex_ring
      {U | U SUBSET S}
      (\U. ring_sum complex_ring U I)
  )
`;;

(* ===== pi is transcendental *)

let pi_is_transcendental = `
  ~(algebraic_number(Cx pi))
`;;

(* ===== more on monomials *)

let monomial_pow = new_definition `
  monomial_pow (m:V->num) (e:num)
  = (\v. e * m v)
`;;

let monomial_product = new_definition `
  monomial_product (S:X->bool) (m:X->V->num)
  = (\v. nsum S (\x. m x v))
`;;

let finite_monomial_vars_permutation = `
  !m:V->num f:V->V.
  f permutes (:V) ==>
  (
    FINITE(monomial_vars (m o f)) <=>
    FINITE(monomial_vars m)
  )
`;;

let finite_monomial_vars_swap = `
  !m:num->num i.
  FINITE(monomial_vars (m o swap(i,i+1))) <=>
  FINITE(monomial_vars m)
`;;

let monomial_eq_swap = `
  !m:V->num i j.
  m o swap(i,j) = m <=>
  m i = m j
`;;

let monomial_le_swap = `
  !m:num->num i.
  FINITE(monomial_vars m) ==>
  ( monomial_le (<=) (m o swap(i,i+1)) m <=>
    m i <= m(i+1)
  )
`;;

let monomial_induction = `
  !P:(num->num)->bool.
  (!n. (!m. monomial_lt (<=) m n ==> P m) ==> P n) ==>
  (!n. P n)
`;;

let monomial_le_mul2_eq = `
  !m n M N:num->num.
  monomial_le (<=) m M ==>
  monomial_le (<=) n N ==>
  monomial_mul m n = monomial_mul M N ==>
  ( m = M /\ n = N )
`;;

let monomial_pow_0 = `
  !m:V->num.
  monomial_pow m 0 = monomial_1
`;;

let monomial_pow_1 = `
  !m:V->num.
  monomial_pow m 1 = m
`;;

let monomial_pow_add = `
  !m:V->num d e.
  monomial_pow m (d+e)
  = monomial_mul (monomial_pow m d) (monomial_pow m e)
`;;

let monomial_1_le = `
  !m.
  monomial (:num) m ==>
  monomial_le (<=) monomial_1 m
`;;

let monomial_product_empty = `
  monomial_product ({}:X->bool) (m:X->V->num)
  = monomial_1
`;;

let monomial_product_insert = `
  !(S:X->bool) (m:X->V->num) t.
  FINITE S ==>
  ~(t IN S) ==>
  monomial_product (t INSERT S) m
  = monomial_mul (m t) (monomial_product S m)
`;;

(* ===== support *)

let support_lt = new_definition `
  support_lt (r:R ring) (p:(num->num)->R) (M:num->num)
  <=> (!m. ~(p m = ring_0 r) ==> monomial_lt (<=) m M)
`;;

let support_le = new_definition `
  support_le (r:R ring) (p:(num->num)->R) (M:num->num)
  <=> (!m. ~(p m = ring_0 r) ==> monomial_le (<=) m M)
`;;

let support_le1 = new_definition `
  support_le1 (r:R ring) (p:(num->num)->R) (M:num->num)
  <=> ( support_le r p M /\ p M = ring_1 r )
`;;

(* POLY_TOP_MONOMIAL_LE is deg first *)
let poly_first_monomial = `
  !(r:R ring) p:(num->num)->R.
  ring_polynomial r p ==>
  ~(p = poly_0 r) ==>
  (?t. ~(p t = ring_0 r) /\ support_le r p t)
`;;

let support_le_0 = `
  !(r:R ring).
  support_le r (poly_0 r) monomial_1
`;;

let support_le_exists = `
  !(r:R ring) p:(num->num)->R.
  ring_polynomial r p ==>
  ?t. support_le r p t
`;;

let support_le_mul = `
  !(r:R ring) p q M N.
  ring_polynomial r p ==>
  ring_polynomial r q ==>
  support_le r p M ==>
  support_le r q N ==>
  support_le r (poly_mul r p q) (monomial_mul M N)
`;;

let support_le_mul_top = `
  !(r:R ring) p q M N.
  ring_polynomial r p ==>
  ring_polynomial r q ==>
  support_le r p M ==>
  support_le r q N ==>
  (poly_mul r p q) (monomial_mul M N)
  = ring_mul r (p M) (q N)
`;;

let support_le1_mul = `
  !(r:R ring) p q M N.
  ring_polynomial r p ==>
  ring_polynomial r q ==>
  support_le1 r p M ==>
  support_le1 r q N ==>
  support_le1 r (poly_mul r p q) (monomial_mul M N)
`;;

let support_le_poly_1 = `
  !(r:R ring) m.
  monomial (:num) m ==>
  support_le r (poly_1 r) m
`;;

let support_le1_poly_1 = `
  !(r:R ring).
  support_le1 r (poly_1 r) monomial_1
`;;

let support_le1_pow = `
  !(r:R ring) p M e.
  ring_polynomial r p ==>
  support_le1 r p M ==>
  support_le1 r (poly_pow r p e) (monomial_pow M e)
`;;

let support_le1_product = `
  !(r:R ring) p M S.
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial r (p s)) ==>
  (!s:X. s IN S ==> support_le1 r (p s) (M s)) ==>
  support_le1 r (ring_product(poly_ring r (:num)) S p) (monomial_product S M)
`;;

let support_le_cancel = `
  !(r:R ring) p q M.
  ring_polynomial r p ==>
  ring_polynomial r q ==>
  support_le r p M ==>
  support_le1 r q M ==>
  support_lt r (poly_sub r p (poly_mul r (poly_const r (p M)) q)) M
`;;

(* ===== symmetric functions *)

let elementary_sympoly_range = new_definition `
  elementary_sympoly_range (r:R ring) n d
  = \m. if ?U. U SUBSET range n /\
               CARD U = d /\
               m = (\i. if i IN U then 1 else 0)
        then ring_1 r
        else ring_0 r
`;;

let elementary_sympoly_range_subring = `
  !(r:R ring) G n d.
  elementary_sympoly_range(subring_generated r G) n d
  = elementary_sympoly_range r n d
`;;

let powerseries_elementary_sympoly_range = `
  !(r:R ring) n d.
  ring_powerseries r (elementary_sympoly_range r n d)
`;;

let polynomial_elementary_sympoly_range = `
  !(r:R ring) n d.
  ring_polynomial r (elementary_sympoly_range r n d)
`;;

let elementary_sympoly_range_in_poly_ring = `
  !(r:R ring) n d.
  elementary_sympoly_range r n d IN ring_carrier(poly_ring r (range n))
`;;

let eval_elementary_sympoly_range = `
  !(r:R ring) n d c.
  (!i. i < n ==> c i IN ring_carrier r) ==>
  poly_evaluate r (elementary_sympoly_range r n d) c
  = ring_sum r {U | U SUBSET range n /\ CARD U = d} (\U. ring_product r U c)
`;;

let eval_elementary_sympoly_range_coeff = `
  !(r:R ring) n d c.
  (!i. i < n ==> c i IN ring_carrier r) ==>
  d <= n ==>
  poly_evaluate r (elementary_sympoly_range r n d) c
  = ring_mul r (
    ring_pow r (ring_neg r (ring_1 r)) d
  ) (
    coeff (n - d) (monic_vanishing_at r (range n) c)
  )
`;;

let elementary_sympoly_range_o_permutes = `
  !(r:R ring) n d f m.
  f permutes range n ==>
  elementary_sympoly_range r n d (m o f)
  = elementary_sympoly_range r n d m
`;;

let elementary_sympoly_range_le = `
  !(r:R ring) n d m.
  ~(elementary_sympoly_range r n d m = ring_0 r) ==>
  monomial_le (<=) m (\i. if n-d <= i /\ i < n then 1 else 0)
`;;

let support_le_elementary_sympoly_range = `
  !(r:R ring) n d.
  support_le r
    (elementary_sympoly_range r n d)
    (\i. if n-d <= i /\ i < n then 1 else 0)
`;;

let support_le1_elementary_sympoly_range = `
  !(r:R ring) n d.
  d <= n ==>
  support_le1 r
    (elementary_sympoly_range r n d)
    (\i. if n-d <= i /\ i < n then 1 else 0)
`;;

let support_le1_pow_elementary_sympoly_range = `
  !(r:R ring) n d e.
  d <= n ==>
  support_le1 r
    (poly_pow r (elementary_sympoly_range r n d) e)
    (\i. if n-d <= i /\ i < n then e else 0)
`;;

let support_le1_product_pow_elementary_sympoly_range = `
  !(r:R ring) n e.
  support_le1 r
    (ring_product(poly_ring r (:num))
      (1..n)
      (\d. poly_pow r (elementary_sympoly_range r n d) (e d))
    )
    (\i. nsum (1..n) (\d. if n-d <= i /\ i < n then e d else 0))
`;;

let support_le1_product_pow_elementary_sympoly_range_v2 = `
  !(r:R ring) n e.
  support_le1 r
    (ring_product(poly_ring r (:num))
      (1..n)
      (\d. poly_pow r (elementary_sympoly_range r n d) (e d))
    )
    (\i. if i < n then nsum (n-i..n) e else 0)
`;;

let symmetric_subring_if_poly_subring_lemma = `
  !(r:R ring) G n c:num->R M p.
  (!i. i < n ==> c i IN ring_carrier r) ==>
  (!d. coeff d (monic_vanishing_at r (range n) c) IN ring_carrier(subring_generated r G)) ==>
  ring_polynomial(subring_generated r G) p ==>
  poly_vars r p SUBSET range n ==>
  (!f m. f permutes range n ==>
         p(m o f) = p(m)) ==>
  support_le r p M ==>
  poly_evaluate r p c IN ring_carrier(subring_generated r G)
`;;

let symmetric_subring_if_poly_subring_range = `
  !(r:R ring) G n c:num->R p.
  (!i. i < n ==> c i IN ring_carrier r) ==>
  (!d. coeff d (monic_vanishing_at r (range n) c) IN ring_carrier(subring_generated r G)) ==>
  ring_polynomial(subring_generated r G) p ==>
  poly_vars r p SUBSET range n ==>
  (!f m. f permutes range n ==>
         p(m o f) = p(m)) ==>
  poly_evaluate r p c IN ring_carrier(subring_generated r G)
`;;

(* ===== poly_reindex: reindexing polynomial variables *)

let poly_vars_poly_reindex = `
  !(r:R ring) A B q f:X->Y.
  BIJ f A B ==>
  poly_vars r q SUBSET B ==>
  poly_vars r (poly_reindex r q f A B) SUBSET A
`;;

let powerseries_poly_reindex = `
  !(r:R ring) A B q f:X->Y.
  BIJ f A B ==>
  ring_powerseries r q ==>
  ring_powerseries r (poly_reindex r q f A B)
`;;

let monomials_poly_reindex = `
  !(r:R ring) A B q f:X->Y.
  BIJ f A B ==>
  ring_powerseries r q ==>
  poly_vars r q SUBSET B ==>
  {m | ~((poly_reindex r q f A B) m = ring_0 r)}
  = IMAGE
      (\m:Y->num. \a:X. if a IN A then m (f a) else 0)
      {m | ~(q m = ring_0 r)}
`;;

let polynomial_poly_reindex = `
  !(r:R ring) A B q f:X->Y.
  BIJ f A B ==>
  ring_polynomial r q ==>
  poly_vars r q SUBSET B ==>
  ring_polynomial r (poly_reindex r q f A B)
`;;

let poly_reindex_permutes = `
  !(r:R ring) A B q f:X->Y.
  BIJ f A B ==>
  ring_polynomial r q ==>
  (!h m. h permutes B ==>
         q(m o h) = q(m)) ==>
  (!g m. g permutes A ==>
         (poly_reindex r q f A B)(m o g)
         = (poly_reindex r q f A B)(m))
`;;

let poly_evaluate_poly_reindex = `
  !(r:R ring) A B q f:X->Y c:Y->R.
  BIJ f A B ==>
  ring_polynomial r q ==>
  poly_vars r q SUBSET B ==>
  poly_evaluate r (poly_reindex r q f A B) (c o f)
  = poly_evaluate r q c
`;;

let poly_reindex_subring = `
  !(r:R ring) G A B q f:X->Y.
  poly_reindex(subring_generated r G) q f A B
  = poly_reindex r q f A B
`;;

let symmetric_subring_if_poly_subring = `
  !(r:R ring) G S c:X->R q.
  FINITE S ==>
  (!s. s IN S ==> c s IN ring_carrier r) ==>
  (!d. coeff d (monic_vanishing_at r S c) IN ring_carrier(subring_generated r G)) ==>
  ring_polynomial(subring_generated r G) q ==>
  poly_vars r q SUBSET S ==>
  (!f m. f permutes S ==>
         q(m o f) = q(m)) ==>
  poly_evaluate r q c IN ring_carrier(subring_generated r G)
`;;

(* ===== ring_ord *)
(* XXX: should factor poly_ord and some of the UFD theorems above via this *)

let ring_ord = new_definition `
  ring_ord (r:R ring) (p:R) (a:R)
  = @e:num. (
      ?u:R. (
        u IN ring_carrier r /\
        ~(ring_divides r p u) /\
        a = ring_mul r (ring_pow r p e) u
      )
    )
`;;

(* could prove via ring_ord_unit *)
let ring_ord_1 = `
  !(r:R ring) p.
  p IN ring_carrier r ==>
  ~(ring_unit r p) ==>
  ring_ord r p (ring_1 r) = 0
`;;

let ring_ord_notdivides = `
  !(r:R ring) p v.
  p IN ring_carrier r ==>
  v IN ring_carrier r ==>
  ~(ring_divides r p v) ==>
  ring_ord r p v = 0
`;;

let ring_ord_unit = `
  !(r:R ring) p v.
  p IN ring_carrier r ==>
  ~(ring_unit r p) ==>
  ring_unit r v ==>
  ring_ord r p v = 0
`;;

let ring_ord_pow_refl = `
  !(r:R ring) p e.
  integral_domain r ==>
  p IN ring_carrier r ==>
  ~(ring_unit r p) ==>
  ~(p = ring_0 r) ==>
  ring_ord r p (ring_pow r p e) = e
`;;

let ring_ord_refl = `
  !(r:R ring) p.
  integral_domain r ==>
  p IN ring_carrier r ==>
  ~(ring_unit r p) ==>
  ~(p = ring_0 r) ==>
  ring_ord r p p = 1
`;;

let ring_ord_exists = `
  !(r:R ring) p.
  integral_domain r ==>
  (noetherian_ring r \/ UFD r) ==>
  p IN ring_carrier r ==>
  ~(ring_unit r p) ==>
  !a.
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  ?e u:R. (
    u IN ring_carrier r /\
    ~(ring_divides r p u) /\
    a = ring_mul r (ring_pow r p e) u
  )
`;;

let ring_ord_unique_lemma = `
  !(r:R ring) p e f u v.
  integral_domain r ==>
  p IN ring_carrier r ==>
  u IN ring_carrier r ==>
  v IN ring_carrier r ==>
  ring_prime r p ==>
  ~(ring_divides r p v) ==>
  ring_mul r (ring_pow r p e) u
  = ring_mul r (ring_pow r p f) v
  ==> e <= f
`;;

let ring_ord_unique = `
  !(r:R ring) p e f u v.
  integral_domain r ==>
  p IN ring_carrier r ==>
  u IN ring_carrier r ==>
  v IN ring_carrier r ==>
  ring_prime r p ==>
  ~(ring_divides r p u) ==>
  ~(ring_divides r p v) ==>
  ring_mul r (ring_pow r p e) u
  = ring_mul r (ring_pow r p f) v
  ==> e = f
`;;

let ring_ord_exists_unique = `
  !(r:R ring) p a.
  integral_domain r ==>
  (noetherian_ring r \/ UFD r) ==>
  ring_prime r p ==>
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  ?u:R. (
    u IN ring_carrier r /\
    ~(ring_divides r p u) /\
    a = ring_mul r (ring_pow r p (ring_ord r p a)) u
  )
`;;

let divides_pow_ring_ord = `
  !(r:R ring) p a.
  integral_domain r ==>
  (noetherian_ring r \/ UFD r) ==>
  ring_prime r p ==>
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  ring_divides r (ring_pow r p (ring_ord r p a)) a
`;;

let divides_le_pow_ring_ord = `
  !(r:R ring) p a e.
  integral_domain r ==>
  (noetherian_ring r \/ UFD r) ==>
  ring_prime r p ==>
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  e <= ring_ord r p a ==>
  ring_divides r (ring_pow r p e) a
`;;

let nonzero_ring_ord_if_divides = `
  !(r:R ring) p a.
  integral_domain r ==>
  (noetherian_ring r \/ UFD r) ==>
  ring_prime r p ==>
  ~(a = ring_0 r) ==>
  ring_divides r p a ==>
  ~(ring_ord r p a = 0)
`;;

let ring_ord_mul = `
  !(r:R ring) p a b.
  integral_domain r ==>
  (noetherian_ring r \/ UFD r) ==>
  ring_prime r p ==>
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  b IN ring_carrier r ==>
  ~(b = ring_0 r) ==>
  ring_ord r p (ring_mul r a b)
  = (ring_ord r p a) + (ring_ord r p b)
`;;

let ring_ord_pow = `
  !(r:R ring) p a e.
  integral_domain r ==>
  (noetherian_ring r \/ UFD r) ==>
  ring_prime r p ==>
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  ring_ord r p (ring_pow r a e)
  = e * ring_ord r p a
`;;

let ring_ord_product_waterfall = `
  !(r:R ring) p a.
  integral_domain r ==>
  (noetherian_ring r \/ UFD r) ==>
  ring_prime r p ==>
  !S.
  FINITE S ==>
  (!s:X. s IN S ==> a s IN ring_carrier r) ==>
  (!s:X. s IN S ==> ~(a s = ring_0 r)) ==>
  ring_ord r p (ring_product r S a)
  = nsum S (\s. ring_ord r p (a s))
`;;

let ring_ord_product = `
  !(r:R ring) p S a.
  integral_domain r ==>
  (noetherian_ring r \/ UFD r) ==>
  ring_prime r p ==>
  FINITE S ==>
  (!s:X. s IN S ==> a s IN ring_carrier r) ==>
  (!s:X. s IN S ==> ~(a s = ring_0 r)) ==>
  ring_ord r p (ring_product r S a)
  = nsum S (\s. ring_ord r p (a s))
`;;

let ring_ord_divides = `
  !(r:R ring) p a b.
  integral_domain r ==>
  (noetherian_ring r \/ UFD r) ==>
  ring_prime r p ==>
  ~(b = ring_0 r) ==>
  ring_divides r a b ==>
  ring_ord r p a <= ring_ord r p b
`;;

let ring_ord_prime_divides = `
  !(r:R ring) p b.
  integral_domain r ==>
  (noetherian_ring r \/ UFD r) ==>
  ring_prime r p ==>
  ~(b = ring_0 r) ==>
  ring_divides r p b ==>
  1 <= ring_ord r p b
`;;

let ring_ord_gcd = `
  !(r:R ring) p a b.
  UFD r ==>
  ring_prime r p ==>
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  b IN ring_carrier r ==>
  ~(b = ring_0 r) ==>
  ring_ord r p (ring_gcd r (a,b))
  = MIN (ring_ord r p a) (ring_ord r p b)
`;;

let ring_ord_associates = `
  !(r:R ring) p a b.
  UFD r ==>
  ring_prime r p ==>
  ring_associates r a b ==>
  ~(a = ring_0 r) ==>
  ring_ord r p a = ring_ord r p b
`;;

let ring_associates_ord = `
  !(r:R ring) p q a.
  UFD r ==>
  ring_prime r p ==>
  ring_associates r p q ==>
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  ring_ord r p a = ring_ord r q a
`;;

let ring_ord_prime = `
  !(r:R ring) p q.
  UFD r ==>
  ring_prime r p ==>
  ring_prime r q ==>
  ring_ord r p q
  = if ring_associates r p q then 1 else 0
`;;

let primefact_ord_waterfall = `
  !(r:R ring).
  UFD r ==>
  !a.
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  (?n q.
    (!i. i IN (1..n) ==> ring_prime r (q i)) /\
    (!i. i IN (1..n) ==> ring_divides r (q i) a) /\
    (!i j. i IN (1..n) ==> j IN (1..n) ==> ring_associates r (q i) (q j) ==> i = j) /\
    ring_associates r a (ring_product r (1..n) (\i. ring_pow r (q i) (ring_ord r (q i) a)))
  )
`;;

let primefact_ord = `
  !(r:R ring) a.
  UFD r ==>
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  (?n q.
    (!i. i IN (1..n) ==> ring_prime r (q i)) /\
    (!i. i IN (1..n) ==> ring_divides r (q i) a) /\
    (!i j. i IN (1..n) ==> j IN (1..n) ==> ring_associates r (q i) (q j) ==> i = j) /\
    ring_associates r a (ring_product r (1..n) (\i. ring_pow r (q i) (ring_ord r (q i) a)))
  )
`;;

let primefact_divides = `
  !(r:R ring) n q e b.
  UFD r ==>
  (!i. i IN 1..n ==> ring_prime r (q i)) ==>
  (!i j. i IN 1..n ==> j IN (1..n) ==> ring_associates r (q i) (q j) ==> i = j) ==>
  b IN ring_carrier r ==>
  ~(b = ring_0 r) ==>
  (!i. i IN 1..n ==> e i <= ring_ord r (q i) b) ==>
  ring_divides r (
    ring_product r (1..n) (\i. ring_pow r (q i) (e i))
  ) b
`;;

let ring_ord_divides_eq = `
  !(r:R ring) a b.
  UFD r ==>
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  b IN ring_carrier r ==>
  ~(b = ring_0 r) ==>
  ( ring_divides r a b <=>
    (!p. ring_prime r p ==>
         ring_ord r p a <= ring_ord r p b
    )
  )
`;;

let ring_ord_associates_eq = `
  !(r:R ring) a b.
  UFD r ==>
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  b IN ring_carrier r ==>
  ~(b = ring_0 r) ==>
  ( ring_associates r a b <=>
    (!p. ring_prime r p ==>
         ring_ord r p a = ring_ord r p b
    )
  )
`;;

(* ===== lcm *)

let lcm_exists = `
  !(r:R ring) a b.
  UFD r ==>
  a IN ring_carrier r ==>
  b IN ring_carrier r ==>
  ?c. (
    c IN ring_carrier r /\
    ring_divides r a c /\
    ring_divides r b c /\
    (!d. d IN ring_carrier r ==>
         ring_divides r a d ==>
         ring_divides r b d ==>
         ring_divides r c d
    )
  )
`;;

let lcm_set_exists = `
  !(r:R ring) a S.
  FINITE S ==>
  UFD r ==>
  (!s:X. s IN S ==> a s IN ring_carrier r) ==>
  ?c. (
    c IN ring_carrier r /\
    (!s. s IN S ==> ring_divides r (a s) c) /\
    (!d. d IN ring_carrier r ==>
         (!s. s IN S ==> ring_divides r (a s) d) ==>
         ring_divides r c d
    )
  )
`;;

let lcm_set_units = `
  !(r:R ring) a S c.
  (!s:X. s IN S ==> a s IN ring_carrier r) ==>
  (!d. d IN ring_carrier r ==>
       (!s. s IN S ==> ring_divides r (a s) d) ==>
       ring_divides r c d
  ) ==>
  (!s. s IN S ==> ring_unit r (a s)) ==>
  ring_unit r c
`;;

let zero_lcm_set = `
  !(r:R ring) a S c.
  integral_domain r ==>
  FINITE S ==>
  (!s:X. s IN S ==> a s IN ring_carrier r) ==>
  c IN ring_carrier r ==>
  (!s. s IN S ==> ring_divides r (a s) c) ==>
  (!d. d IN ring_carrier r ==>
       (!s. s IN S ==> ring_divides r (a s) d) ==>
       ring_divides r c d
  ) ==>
  ( c = ring_0 r <=>
    ( ?s. s IN S /\ a s = ring_0 r )
  )
`;;

(* could extract from zero_lcm_set *)
let zero_lcm = `
  !(r:R ring) a b.
  integral_domain r ==>
  ring_divides r a c ==>
  ring_divides r b c ==>
  (!d. d IN ring_carrier r ==>
       ring_divides r a d ==>
       ring_divides r b d ==>
       ring_divides r c d
  ) ==>
  ( c = ring_0 r <=>
    ( a = ring_0 r \/ b = ring_0 r )
  )
`;;

let ring_ord_lcm_set = `
  !(r:R ring) a S c p t.
  UFD r ==>
  (!s:X. s IN S ==> a s IN ring_carrier r) ==>
  c IN ring_carrier r ==>
  (!s. s IN S ==> ring_divides r (a s) c) ==>
  (!d. d IN ring_carrier r ==>
       (!s. s IN S ==> ring_divides r (a s) d) ==>
       ring_divides r c d
  ) ==>
  ~(c = ring_0 r) ==>
  ring_prime r p ==>
  t IN S ==>
  (!s:X. s IN S ==> ring_ord r p (a s) <= ring_ord r p (a t)) ==>
  ring_ord r p c = ring_ord r p (a t)
`;;

let ring_ord_lcm = `
  !(r:R ring) a b c p.
  UFD r ==>
  ring_divides r a c ==>
  ring_divides r b c ==>
  (!d. d IN ring_carrier r ==>
       ring_divides r a d ==>
       ring_divides r b d ==>
       ring_divides r c d
  ) ==>
  ~(c = ring_0 r) ==>
  ring_prime r p ==>
  ring_ord r p c
  = MAX (ring_ord r p a) (ring_ord r p b)
`;;

let ring_ord_squarefree = `
  !(r:R ring) a.
  UFD r ==>
  a IN ring_carrier r ==>
  ~(a = ring_0 r) ==>
  ( ring_squarefree r a <=>
    (!p. ring_prime r p ==>
         ring_ord r p a <= 1
    )
  )
`;;

let ring_squarefree_lcm = `
  !(r:R ring) a b c.
  UFD r ==>
  ring_divides r a c ==>
  ring_divides r b c ==>
  (!d. d IN ring_carrier r ==>
       ring_divides r a d ==>
       ring_divides r b d ==>
       ring_divides r c d
  ) ==>
  ~(c = ring_0 r) ==>
  ring_squarefree r a ==>
  ring_squarefree r b ==>
  ring_squarefree r c
`;;

let ring_squarefree_lcm_set = `
  !(r:R ring) a S c.
  UFD r ==>
  (!s:X. s IN S ==> a s IN ring_carrier r) ==>
  c IN ring_carrier r ==>
  (!s. s IN S ==> ring_divides r (a s) c) ==>
  (!d. d IN ring_carrier r ==>
       (!s. s IN S ==> ring_divides r (a s) d) ==>
       ring_divides r c d
  ) ==>
  ~(c = ring_0 r) ==>
  (!s. s IN S ==> ring_squarefree r (a s)) ==>
  ring_squarefree r c
`;;

let ring_prime_divides_lcm_set = `
  !(r:R ring) a S c p.
  UFD r ==>
  (!s:X. s IN S ==> a s IN ring_carrier r) ==>
  c IN ring_carrier r ==>
  (!s. s IN S ==> ring_divides r (a s) c) ==>
  (!d. d IN ring_carrier r ==>
       (!s. s IN S ==> ring_divides r (a s) d) ==>
       ring_divides r c d
  ) ==>
  ~(c = ring_0 r) ==>
  ring_prime r p ==>
  ( ring_divides r p c <=>
    (?s. s IN S /\ ring_divides r p (a s))
  )
`;;

(* ===== polynomial lcm *)

let poly_lcm_set_exists = `
  !(r:R ring) a S.
  field r ==>
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial r (a s)) ==>
  ?c. (
    ring_polynomial r c /\
    (!s. s IN S ==> ring_divides(x_poly r) (a s) c) /\
    (!d. ring_polynomial r d ==>
         (!s. s IN S ==> ring_divides(x_poly r) (a s) d) ==>
         ring_divides(x_poly r) c d
    )
  )
`;;

let monic_lcm_set_exists = `
  !(r:R ring) a S.
  field r ==>
  FINITE S ==>
  (!s:X. s IN S ==> ring_polynomial r (a s)) ==>
  (!s:X. s IN S ==> ~(a s = poly_0 r)) ==>
  ?c. (
    ring_polynomial r c /\
    monic r c /\
    (!s. s IN S ==> ring_divides(x_poly r) (a s) c) /\
    (!d. ring_polynomial r d ==>
         (!s. s IN S ==> ring_divides(x_poly r) (a s) d) ==>
         ring_divides(x_poly r) c d
    )
  )
`;;

(* ===== more on algebraic numbers *)

let minimal_squarefree_from_algebraic_set = `
  !S.
  FINITE S ==>
  S SUBSET algebraic_number ==>
  (?p.
    ring_polynomial QinC_ring p /\
    ring_squarefree(x_poly QinC_ring) p /\
    monic QinC_ring p /\
    S SUBSET complex_root p /\
    (!z. complex_root p z ==> (?s. s IN S /\ minimal_polynomial s = minimal_polynomial z))
  )
`;;

let squarefree_from_algebraic_set = `
  !S.
  FINITE S ==>
  S SUBSET algebraic_number ==>
  (?p.
    ring_polynomial QinC_ring p /\
    ring_squarefree(x_poly QinC_ring) p /\
    monic QinC_ring p /\
    S SUBSET complex_root p
  )
`;;

let squarefree_from_algebraic_set_avoiding_0 = `
  !S.
  FINITE S ==>
  S SUBSET algebraic_number ==>
  ~(Cx(&0) IN S) ==>
  (?p.
    ring_polynomial QinC_ring p /\
    ring_squarefree(x_poly QinC_ring) p /\
    monic QinC_ring p /\
    S SUBSET complex_root p /\
    ~(complex_root p (Cx(&0)))
  )
`;;

(* ===== more on multivariate polynomials *)

let poly_vars_sum_poly_subset = `
  !(r:R ring) p:X->(V->num)->R U S.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  (!s. s IN S ==> poly_vars r (p s) SUBSET U) ==>
  poly_vars r (ring_sum(poly_ring r (:V)) S p) SUBSET U
`;;

let poly_vars_product_poly_subset = `
  !(r:R ring) p:X->(V->num)->R U S.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  (!s. s IN S ==> poly_vars r (p s) SUBSET U) ==>
  poly_vars r (ring_product(poly_ring r (:V)) S p) SUBSET U
`;;

let poly_vars_pow = `
  !(r:R ring) p:(V->num)->R n.
  ring_powerseries r p ==>
  poly_vars r (poly_pow r p n)
  SUBSET poly_vars r p
`;;

let poly_vars_pow_subset = `
  !(r:R ring) p:(V->num)->R n U.
  ring_powerseries r p ==>
  poly_vars r p SUBSET U ==>
  poly_vars r (poly_pow r p n) SUBSET U
`;;

let poly_evaluate_pow = `
  !(r:R ring) p:(V->num)->R q:V->R n.
  ring_polynomial r p ==>
  (!i. i IN poly_vars r p ==> q i IN ring_carrier r) ==>
  poly_evaluate r (poly_pow r p n) q
  = ring_pow r (poly_evaluate r p q) n
`;;

let poly_evaluate_sum = `
  !(r:R ring) p:X->(V->num)->R q:V->R S:X->bool.
  FINITE S ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  poly_evaluate r (ring_sum(poly_ring r (:V)) S p) q
  = ring_sum r S (\s. poly_evaluate r (p s) q)
`;;

(* XXX: limit q v condition to variables appearing *)
let poly_evaluate_product = `
  !(r:R ring) p:X->(V->num)->R q:V->R S:X->bool.
  FINITE S ==>
  (!v. q v IN ring_carrier r) ==>
  (!s. s IN S ==> ring_polynomial r (p s)) ==>
  poly_evaluate r (ring_product(poly_ring r (:V)) S p) q
  = ring_product r S (\s. poly_evaluate r (p s) q)
`;;

(* ===== vandermonde *)

(* can prove this via det *)
(* or via transpose and monic_vanishing_at *)
let vandermonde_indep_range = `
  !(r:R ring) n c v.
  integral_domain r ==>
  (!i. i < n ==> c i IN ring_carrier r) ==>
  (!i. i < n ==> v i IN ring_carrier r) ==>
  (!i j. i < n ==> j < n ==> v i = v j ==> i = j) ==>
  (!e. e < n ==> ring_sum r (range n) (\i. ring_mul r (c i) (ring_pow r (v i) e)) = ring_0 r) ==>
  (!i. i < n ==> c i = ring_0 r)
`;;

let vandermonde_indep = `
  !(r:R ring) S c v.
  integral_domain r ==>
  FINITE S ==>
  (!s:X. s IN S ==> c s IN ring_carrier r) ==>
  (!s. s IN S ==> v s IN ring_carrier r) ==>
  (!s t. s IN S ==> t IN S ==> v s = v t ==> s = t) ==>
  (!e. e < CARD S ==> ring_sum r S (\s. ring_mul r (c s) (ring_pow r (v s) e)) = ring_0 r) ==>
  (!s. s IN S ==> c s = ring_0 r)
`;;

let expformal_linearly_independent = `
  !S:complex->bool B:complex->complex.
  FINITE S ==>
  poly_sum complex_ring S (
    \z. poly_mul complex_ring (
      poly_const complex_ring (B z)
    ) (
      expformal z
    )
  ) = poly_0 complex_ring ==>
  (!z. z IN S ==> B z = Cx(&0))
`;;

let expformal_perm_linearly_independent = `
  !S:complex->bool B:complex->complex i:complex->complex.
  FINITE S ==>
  i permutes S ==>
  poly_sum complex_ring S (
    \z. poly_mul complex_ring (
      poly_const complex_ring (B z)
    ) (
      expformal (i z)
    )
  ) = poly_0 complex_ring ==>
  (!z. z IN S ==> B z = Cx(&0))
`;;

(* ===== expanding prod_pi sum c_z exp(pi(z)) *)

let ring_product_perm_sum_mul_exp_expand = `
  !(a:A ring) (b:B ring) E:A->B c:A->B S:A->bool.
  (!x:A. x IN ring_carrier a ==>
         E x IN ring_carrier b) ==>
  E(ring_0 a) = ring_1 b ==>
  (!x y:A. E(ring_add a x y)
           = ring_mul b (E x) (E y)) ==>
  FINITE S ==>
  S SUBSET ring_carrier a ==>
  (!s:A. s IN S ==> c s IN ring_carrier b) ==>
  ring_product b (perm S) (
    \i. ring_sum b S (
      \z. ring_mul b (c z) (E(i z))
    )
  )
  =
  ring_sum b (
    IMAGE (\f. numpreimages f (perm S)) (functions (perm S) S)
  ) (
    \e.
      ring_mul b (
        ring_product b {y | ~(e y = 0)} (
          \y. ring_pow b (c y) (e y)
        )
      ) (
        ring_sum b {f | f IN functions (perm S) S /\ numpreimages f (perm S) = e} (
          E o (\f. ring_sum a (perm S) (\i. i (f i)))
        )
      )
  )
`;;

let product_perm_sum_mul_cexp_expand = `
  !c:complex->complex S:complex->bool.
  FINITE S ==>
  ring_product complex_ring (perm S) (
    \i. ring_sum complex_ring S (
      \z. ring_mul complex_ring (c z) (cexp(i z))
    )
  )
  =
  ring_sum complex_ring (
    IMAGE (\f. numpreimages f (perm S)) (functions (perm S) S)
  ) (
    \e.
      ring_product complex_ring {y | ~(e y = 0)} (
        \y. (c y) pow (e y)
      )
      *
      ring_sum complex_ring {f | f IN functions (perm S) S /\ numpreimages f (perm S) = e} (
        cexp o (\f. ring_sum complex_ring (perm S) (\i. i (f i)))
      )
  )
`;;

let product_perm_sum_mul_expformal_expand = `
  !c:complex->((1->num)->complex) S:complex->bool.
  FINITE S ==>
  ring_product(x_series complex_ring) (perm S) (
    \i. ring_sum(x_series complex_ring) S (
      \z. poly_mul complex_ring (c z) (expformal(i z))
    )
  )
  =
  ring_sum(x_series complex_ring) (
    IMAGE (\f. numpreimages f (perm S)) (functions (perm S) S)
  ) (
    \e.
      ring_mul(x_series complex_ring) (
        ring_product(x_series complex_ring) {y | ~(e y = 0)} (
          \y. ring_pow(x_series complex_ring) (c y) (e y)
        )
      ) (
        ring_sum(x_series complex_ring) {f | f IN functions (perm S) S /\ numpreimages f (perm S) = e} (
          expformal o (\f. ring_sum complex_ring (perm S) (\i. i (f i)))
        )
      )
  )
`;;

let product_perm_sum_mul_expformal_expand_v2 = `
  !c:complex->((1->num)->complex) S:complex->bool.
  FINITE S ==>
  ring_product(x_series complex_ring) (perm S) (
    \i. ring_sum(x_series complex_ring) S (
      \z. poly_mul complex_ring (c z) (expformal(i z))
    )
  )
  =
  ring_sum(x_series complex_ring) (
    IMAGE (\f. ring_sum complex_ring (perm S) (\i. i (f i))) (functions (perm S) S)
  ) (\y.
    ring_sum(x_series complex_ring) (
      IMAGE (\f. numpreimages f (perm S)) (functions (perm S) S)
    ) (
      \e.
        poly_mul complex_ring (
          ring_product(x_series complex_ring) {z | ~(e z = 0)} (
            \z. ring_pow(x_series complex_ring) (c z) (e z)
          )
        ) (
          poly_mul complex_ring (
            ring_of_num(x_series complex_ring) (numpreimages (\f. ring_sum complex_ring (perm S) (\i. i (f i))) {f | f IN functions (perm S) S /\ numpreimages f (perm S) = e} y)
          ) (expformal y)
        )
      )
  )
`;;

let product_perm_sum_mul_expformal_expand_v3 = `
  !c:complex->complex S:complex->bool.
  FINITE S ==>
  ring_product(x_series complex_ring) (perm S) (
    \i. ring_sum(x_series complex_ring) S (
      \z. poly_mul complex_ring (poly_const complex_ring (c z)) (expformal(i z))
    )
  )
  =
  ring_sum(x_series complex_ring) (
    IMAGE (\f. ring_sum complex_ring (perm S) (\i. i (f i))) (functions (perm S) S)
  ) (\y.
    poly_mul complex_ring (
      poly_const complex_ring (
        ring_sum complex_ring (
          IMAGE (\f. numpreimages f (perm S)) (functions (perm S) S)
        ) (\e.
          ring_product complex_ring {z | ~(e z = 0)} (
            \z. (c z) pow (e z)
          ) * (
            Cx(&(numpreimages (\f. ring_sum complex_ring (perm S) (\i. i (f i))) {f | f IN functions (perm S) S /\ numpreimages f (perm S) = e} y))
          )
        )
      )
    ) (expformal y)
  )
`;;

(* ===== more general transcendence results, part 1: alpha symmetrization *)

let zero_sum_QinC_exp_squarefree_roots_lemma_sym_powersums = `
  !p e d.
  ring_polynomial QinC_ring p ==>
  ring_squarefree(x_poly QinC_ring) p ==>
  monic QinC_ring p ==>
  ring_sum complex_ring
    {f | f IN functions (perm(complex_root p)) (complex_root p) /\ numpreimages f (perm(complex_root p)) = e}
    (\f. (ring_sum complex_ring (perm(complex_root p)) (\i. i (f i))) pow d)
  IN QinC
`;;

let zero_sum_QinC_exp_squarefree_roots_lemma_sym_coeff_poly = `
  !p e n.
  ring_polynomial QinC_ring p ==>
  ring_squarefree(x_poly QinC_ring) p ==>
  monic QinC_ring p ==>
  coeff n (
    monic_vanishing_at complex_ring
      {f | f IN functions (perm(complex_root p)) (complex_root p) /\ numpreimages f (perm(complex_root p)) = e}
      (\f. (ring_sum complex_ring (perm(complex_root p)) (\i. i (f i))))
  ) IN QinC
`;;

let zero_sum_QinC_exp_squarefree_roots_lemma_sym_poly = `
  !p e.
  ring_polynomial QinC_ring p ==>
  ring_squarefree(x_poly QinC_ring) p ==>
  monic QinC_ring p ==>
  ring_polynomial QinC_ring (
    monic_vanishing_at complex_ring
      {f | f IN functions (perm(complex_root p)) (complex_root p) /\ numpreimages f (perm(complex_root p)) = e}
      (\f. (ring_sum complex_ring (perm(complex_root p)) (\i. i (f i))))
  )
`;;

let zero_sum_QinC_exp_squarefree_roots_lemma_denouement = `
  !S:complex->bool B:complex->complex.
  FINITE S ==>
  ( !a.
    ring_sum complex_ring
      (
        IMAGE
          (\f. numpreimages f (perm S))
          (functions (perm S) S)
      ) (
        \s.
          ring_product complex_ring
            {y | ~(s y = 0)}
            ( \y. (B y) pow (s y))
          * Cx(&(
              numpreimages (
                \f.
                  ring_sum complex_ring
                    (perm S)
                    (\i. i (f i))
              ) {
                f | f IN functions (perm S) (S) /\
                    numpreimages f (perm S) = s
              } a
          ))
      )
    = Cx (&0)
  ) ==>
  (!z. z IN S ==> B z = Cx(&0))
`;;

let zero_sum_QinC_exp_squarefree_roots = `
  !p B.
  ring_polynomial QinC_ring p ==>
  ring_squarefree(x_poly QinC_ring) p ==>
  monic QinC_ring p ==>
  (!z:complex. complex_root p z ==> B z IN QinC) ==>
  ring_sum complex_ring (complex_root p) (\z. (B z) * cexp z) = Cx(&0) ==>
  (!z. complex_root p z ==> B z = Cx(&0))
`;;

let zero_sum_QinC_exp_algebraic = `
  !S B.
  FINITE S ==>
  S SUBSET algebraic_number ==>
  (!s. s IN S ==> B s IN QinC) ==>
  ring_sum complex_ring S (\s. (B s) * cexp s) = Cx(&0) ==>
  (!s. s IN S ==> B s = Cx(&0))
`;;

let transcendental_if_exp_nonzero_algebraic = `
  !a.
  algebraic_number a /\ algebraic_number(cexp a)
  ==> a = Cx(&0)
`;;

(* ===== expanding prod_f sum_y f(y) exp(y) *)

let ring_product_functions_sum_mul_exp_expand = `
  !(a:A ring) (b:B ring) E:A->B c:C->B Y:A->bool Z:C->bool.
  (!x:A. x IN ring_carrier a ==>
         E x IN ring_carrier b) ==>
  E(ring_0 a) = ring_1 b ==>
  (!x y:A. E(ring_add a x y)
           = ring_mul b (E x) (E y)) ==>
  FINITE Y ==>
  FINITE Z ==>
  Y SUBSET ring_carrier a ==>
  IMAGE c Z SUBSET ring_carrier b ==>
  ring_product b (functions Y Z) (
    \f. ring_sum b Y (
      \y. ring_mul b (c (f y)) (E y)
    )
  )
  =
  ring_sum b (
    IMAGE (ring_sum a (functions Y Z)) (functions (functions Y Z) Y)
  ) (
    \z.
      ring_mul b (
        ring_sum b {g |
          g IN functions (functions Y Z) Y /\
          ring_sum a (functions Y Z) g = z
        } (\g.
          ring_product b (functions Y Z) (\f. c(f(g f)))
        )
      ) (E z)
  )
`;;

let product_functions_sum_mul_cexp_expand = `
  !Y:complex->bool Z:complex->bool.
  FINITE Y ==>
  FINITE Z ==>
  ring_product complex_ring (functions Y Z) (
    \f. ring_sum complex_ring Y (
      \y. ring_mul complex_ring (f y) (cexp y)
    )
  )
  =
  ring_sum complex_ring (
    IMAGE (ring_sum complex_ring (functions Y Z)) (functions (functions Y Z) Y)
  ) (
    \z.
      ring_sum complex_ring {g |
        g IN functions (functions Y Z) Y /\
        ring_sum complex_ring (functions Y Z) g = z
      } (\g.
        ring_product complex_ring (functions Y Z) (\f. f(g f))
      )
      * cexp z
  )
`;;

let product_functions_sum_mul_expformal_expand = `
  !Y:complex->bool Z:complex->bool.
  FINITE Y ==>
  FINITE Z ==>
  ring_product(x_series complex_ring) (functions Y Z) (
    \f. ring_sum(x_series complex_ring) Y (
      \y. ring_mul(x_series complex_ring)
            (poly_const complex_ring (f y))
            (expformal y)
    )
  )
  =
  ring_sum(x_series complex_ring) (
    IMAGE (ring_sum complex_ring (functions Y Z)) (functions (functions Y Z) Y)
  ) (
    \z.
      poly_mul complex_ring (
        poly_const complex_ring (
          ring_sum complex_ring {g |
            g IN functions (functions Y Z) Y /\
            ring_sum complex_ring (functions Y Z) g = z
          } (\g.
            ring_product complex_ring (functions Y Z) (\f. f(g f))
          )
        )
      ) (expformal z)
  )
`;;

(* ===== more general transcendence results, part 2: beta symmetrization *)

let zero_sum_nonzero_algebraic_exp_algebraic_lemma_sym = `
  !s S:complex->bool p.
  FINITE S ==>
  ring_polynomial QinC_ring p ==>
  ring_squarefree(x_poly QinC_ring) p ==>
  monic QinC_ring p ==>
  ring_sum complex_ring {g |
    g IN functions (functions S (complex_root p)) S /\
    ring_sum complex_ring (functions S (complex_root p)) g = s
  } (\g.
    ring_product complex_ring (functions S (complex_root p)) (\f. f (g f))
  ) IN QinC
`;;

let zero_sum_nonzero_algebraic_exp_algebraic = `
  !S B.
  FINITE S ==>
  S SUBSET algebraic_number ==>
  (!s. s IN S ==> algebraic_number (B s)) ==>
  (!s. s IN S ==> ~(B s = Cx(&0))) ==>
  ring_sum complex_ring S (\s. (B s) * cexp s) = Cx(&0) ==>
  S = {}
`;;

let zero_sum_algebraic_exp_algebraic = `
  !S B.
  FINITE S /\
  S SUBSET algebraic_number /\
  (!s. s IN S ==> algebraic_number (B s)) /\
  ring_sum complex_ring S (\s. (B s) * cexp s) = Cx(&0) ==>
  (!s. s IN S ==> B s = Cx(&0))
`;;

(* ===== re-print highlighted theorems *)

let e_is_irrational = e_is_irrational;;
let e_is_transcendental = e_is_transcendental;;
let pi_is_transcendental = pi_is_transcendental;;
let transcendental_if_exp_nonzero_algebraic = transcendental_if_exp_nonzero_algebraic;;
let zero_sum_algebraic_exp_algebraic = zero_sum_algebraic_exp_algebraic;;
