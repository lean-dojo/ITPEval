$(
  Statement-only formalization of Thousand Theorems corpus artifact Q172298
  (thousand-theorems__metamath__Q172298), "Lasker--Noether theorem": every
  finite primary decomposition of a submodule over a commutative-semiring
  semimodule can be replaced by one with the same intersection and pairwise
  distinct radicals of its full-module colon ideals. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's SLMod supplies arbitrary semimodules over arbitrary semirings.
  Requiring the multiplicative monoid of Scalar(W) to be commutative gives
  exactly the source's commutative-semiring scalar domain.

  Q172298Submodules W is the set of subsets of Base(W) containing zero and
  closed under vector addition and scalar multiplication. Q172298Inf W s is
  the intersection of the finite family s inside Base(W), including Base(W)
  for the empty family. Q172298Colon W J is the ideal of scalars sending every
  vector into J, exactly J.colon Set.univ in the Lean source, and
  Q172298Radical R I is the usual ideal radical defined by membership of a
  natural power. Q172298Primary W J is the source definition of a proper
  primary submodule.

  The final declaration is the single unproved $a corpus statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q172298Submodules Q172298Inf Q172298Colon Q172298Radical
   Q172298Primary $.

q172298-submodules-syntax $a class ( Q172298Submodules W ) $.
q172298-inf-syntax $a class ( Q172298Inf W s ) $.
q172298-colon-syntax $a class ( Q172298Colon W J ) $.
q172298-radical-syntax $a class ( Q172298Radical R I ) $.
q172298-primary-syntax $a wff ( Q172298Primary W J ) $.

${
  $d J W r x y $.

  q172298-submodules-definition $a |- ( Q172298Submodules W ) =
    {
      J e. ~P ( Base ` W ) |
        (
          ( 0g ` W ) e. J
          /\
          (
            A. x e. J A. y e. J
              ( x ( +g ` W ) y ) e. J
            /\
            A. r e. ( Base ` ( Scalar ` W ) )
              A. x e. J
                ( r ( .s ` W ) x ) e. J
          )
        )
    }
  $.
$}

${
  $d J W s x $.

  q172298-inf-definition $a |- ( Q172298Inf W s ) =
    {
      x e. ( Base ` W ) |
        A. J e. s x e. J
    }
  $.
$}

${
  $d J W r x $.

  q172298-colon-definition $a |- ( Q172298Colon W J ) =
    {
      r e. ( Base ` ( Scalar ` W ) ) |
        A. x e. ( Base ` W )
          ( r ( .s ` W ) x ) e. J
    }
  $.
$}

${
  $d I R n r $.

  q172298-radical-definition $a |- ( Q172298Radical R I ) =
    {
      r e. ( Base ` R ) |
        E. n e. NN0
          ( n ( .g ` ( mulGrp ` R ) ) r ) e. I
    }
  $.
$}

${
  $d J W r x $.

  q172298-primary-definition $a |- (
    ( Q172298Primary W J )
    <->
    (
      J e. ( Q172298Submodules W )
      /\
      (
        J =/= ( Base ` W )
        /\
        A. r e. ( Base ` ( Scalar ` W ) )
          A. x e. ( Base ` W )
            (
              ( r ( .s ` W ) x ) e. J
              ->
              (
                x e. J
                \/
                r e.
                  (
                    Q172298Radical
                    ( Scalar ` W )
                    ( Q172298Colon W J )
                  )
              )
            )
      )
    )
  ) $.
$}

${
  $d I J N W s t $.

  thousand-theorems-q172298-primary-decomposition-distinct-radicals $a |-
    A. W
      (
        (
          W e. SLMod
          /\
          ( mulGrp ` ( Scalar ` W ) ) e. CMnd
        )
        ->
        A. N e. ( Q172298Submodules W )
          A. s
            (
              (
                (
                  s e. Fin
                  /\
                  s C_ ( Q172298Submodules W )
                )
                /\
                (
                  ( Q172298Inf W s ) = N
                  /\
                  A. J e. s ( Q172298Primary W J )
                )
              )
              ->
              E. t
                (
                  (
                    t e. Fin
                    /\
                    t C_ ( Q172298Submodules W )
                  )
                  /\
                  (
                    ( Q172298Inf W t ) = N
                    /\
                    (
                      A. J e. t ( Q172298Primary W J )
                      /\
                      A. I e. t A. J e. t
                        (
                          I =/= J
                          ->
                          (
                            Q172298Radical
                            ( Scalar ` W )
                            ( Q172298Colon W I )
                          )
                          =/=
                          (
                            Q172298Radical
                            ( Scalar ` W )
                            ( Q172298Colon W J )
                          )
                        )
                    )
                  )
                )
            )
      )
  $.
$}
