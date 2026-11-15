$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1996_a3: whether every assignment of subsets of six courses to
  twenty students has five students and two courses chosen by all five or
  by none of the five, with the asserted answer false. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The intervals 1 ... 20 and 1 ... 6 are twenty- and six-element carriers.
  Thus f ranges over every assignment of a subset of the course carrier to
  each student. This directly matches the Lean and Rocq finite-type
  functions; restricting Isabelle's range-constrained natural-indexed
  function to 1 ... 20, and extending any such finite assignment outside
  that interval, gives the same universal proposition.

  The witnesses S and C remain internal existential subsets with cardinalities
  five and two. The two disjuncts state pointwise that every selected course
  belongs to every selected student's choice set, or belongs to none of them.
  The biconditional with F. preserves the supplied solution False. The final
  declaration is an unproved $a statement encoding; this database contains no
  $p proof statement.
$)

${
  $d C S c f s $.

  putnambench-putnam-1996-a3 $a |- (
    (
      A. f e.
        (
          ( ~P ( 1 ... 6 ) )
          ^m
          ( 1 ... ; 2 0 )
        )
        E. S e.
          {
            S e. ~P ( 1 ... ; 2 0 )
            |
            ( # ` S ) = 5
          }
          E. C e.
            {
              C e. ~P ( 1 ... 6 )
              |
              ( # ` C ) = 2
            }
            (
              A. s e. S A. c e. C
                c e. ( f ` s )
              \/
              A. s e. S A. c e. C
                -. c e. ( f ` s )
            )
    )
    <-> F.
  ) $.
$}
