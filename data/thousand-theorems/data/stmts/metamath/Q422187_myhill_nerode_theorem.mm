$(
  Statement-only formalization of Thousand Theorems corpus artifact Q422187
  (thousand-theorems__metamath__Q422187), "Myhill--Nerode theorem": for an
  arbitrary alphabet and language, the language is regular if and only if
  its set of left quotients by finite words is finite. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Word A is SetMM's set of all finite words over the arbitrary alphabet A,
  and L ranges over arbitrary subsets of Word A. Q422187LeftQuotient A L x
  is the language of suffixes y for which x ++ y belongs to L.
  Q422187LeftRange A L is exactly the range of this left-quotient operation.

  Q422187Accepts A Q D q F w says that the word w has a run through the
  deterministic transition function D, starting at q and ending in F.
  Q422187Regular A L internally quantifies the finite state set Q, total
  transition function D, start state q, and accepting-state set F. This is
  the finite-DFA definition of regularity used by the Lean source.

  All declarations preceding the final assertion are syntax or faithful
  definitions. The final $a declaration is the single unproved corpus
  statement, and this root statement file contains no $p proof declaration.
$)

$c Q422187LeftQuotient Q422187LeftRange $.
$c Q422187Accepts Q422187Regular $.

q422187-left-quotient-syntax
  $a class ( Q422187LeftQuotient A L x ) $.
q422187-left-range-syntax
  $a class ( Q422187LeftRange A L ) $.
q422187-accepts-syntax
  $a wff ( Q422187Accepts A Q D q F w ) $.
q422187-regular-syntax
  $a wff ( Q422187Regular A L ) $.

${
  $d A L x y $.

  q422187-left-quotient-definition $a |- (
    Q422187LeftQuotient A L x
  ) = {
    y e. Word A |
    ( x ++ y ) e. L
  } $.
$}

${
  $d A L S x $.

  q422187-left-range-definition $a |- (
    Q422187LeftRange A L
  ) = {
    S e. ( ~P ( Word A ) ) |
    E. x e. Word A
      S = ( Q422187LeftQuotient A L x )
  } $.
$}

${
  $d A D F Q i q r w $.

  q422187-accepts-definition $a |- (
    Q422187Accepts A Q D q F w
  ) <->
  E. r e. Word Q
    (
      ( # ` r ) = ( ( # ` w ) + 1 )
      /\
      (
        ( r ` 0 ) = q
        /\
        (
          A. i e. ( 0 ..^ ( # ` w ) )
            (
              ( r ` ( i + 1 ) )
              =
              ( D ` <. ( r ` i ) , ( w ` i ) >. )
            )
          /\
          ( r ` ( # ` w ) ) e. F
        )
      )
    ) $.
$}

${
  $d A D F L Q q w $.

  q422187-regular-definition $a |- (
    Q422187Regular A L
  ) <->
  E. Q e. Fin
    E. D e. ( ( Q X. A ) --> Q )
      E. q e. Q
        E. F e. ( ~P Q )
          A. w e. Word A
            (
              w e. L
              <->
              ( Q422187Accepts A Q D q F w )
            ) $.
$}

${
  $d A L $.

  thousand-theorems-q422187-myhill-nerode $a |- (
    A. A
      A. L e. ( ~P ( Word A ) )
        (
          ( Q422187Regular A L )
          <->
          ( Q422187LeftRange A L ) e. Fin
        )
  ) $.
$}
