$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1346677
  (thousand-theorems__metamath__Q1346677), "Tietze extension theorem": every
  bounded continuous real-valued function along a closed embedding into a
  normal topological space has a bounded continuous extension with the same
  norm. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1346677Bounded J F says that the real-valued function F is uniformly
  bounded on the full carrier of topology J. Q1346677SupNorm J F is the
  supremum of its pointwise absolute values, with zero adjoined so that the
  empty-domain norm is zero. For a bounded real-valued function this is
  exactly the norm of Lean's bundled bounded continuous function.

  A SetMM topology K in Nrm is a normal topological space. The conjunction
  saying that E is a homeomorphism from J onto the subspace topology of K on
  ran E, and that ran E is closed in K, is equivalent to Lean's
  IsClosedEmbedding E. Continuity uses SetMM's native Cn class and the usual
  norm topology of RRfld. The final $a assertion retains the internal
  existential extension G and contains no $p proof statement.
$)

$c Q1346677Bounded Q1346677SupNorm $.

q1346677-bounded-syntax $a wff ( Q1346677Bounded J F ) $.
q1346677-sup-norm-syntax $a class ( Q1346677SupNorm J F ) $.

${
  $d F J b x $.

  q1346677-bounded-definition $a |- (
    ( Q1346677Bounded J F )
    <->
    E. b e. RR+
      A. x e. U. J
        ( abs ` ( F ` x ) ) <_ b
  ) $.
$}

${
  $d F J x $.

  q1346677-sup-norm-definition $a |-
    ( Q1346677SupNorm J F ) =
      sup (
        ( ran ( x e. U. J |-> ( abs ` ( F ` x ) ) ) u. { 0 } )
        , RR
        , <
      )
  $.
$}

${
  $d E F G J K $.

  thousand-theorems-q1346677-tietze-extension $a |-
    A. J e. Top
      A. K e. Nrm
        A. E
          A. F e. ( J Cn ( TopOpen ` RRfld ) )
            (
              (
                E e. ( J Homeo ( K |`t ran E ) )
                /\
                ran E e. ( Clsd ` K )
                /\
                ( Q1346677Bounded J F )
              )
              ->
              E. G e. ( K Cn ( TopOpen ` RRfld ) )
                (
                  ( Q1346677Bounded K G )
                  /\
                  ( Q1346677SupNorm K G ) =
                    ( Q1346677SupNorm J F )
                  /\
                  ( G o. E ) = F
                )
            )
  $.
$}
