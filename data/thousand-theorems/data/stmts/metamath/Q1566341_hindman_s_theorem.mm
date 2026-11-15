$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1566341
  (thousand-theorems__metamath__Q1566341), "Hindman's theorem": in every
  finite cover of the finite-products set of a stream in an arbitrary
  semigroup, one cover member contains the finite-products set of another
  stream. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, G e. Smgrp supplies an arbitrary semigroup, Base ` G is its
  carrier, and a member of ( ( Base ` G ) ^m NN0 ) is an infinite stream.
  Q1566341FP G A is the set of products G gsum ( A o. f ) over all nonempty
  finite strictly increasing index maps f. Thus it is exactly the set of
  left-to-right products of nonempty finite subsequences, bidirectionally
  equivalent to the inductive Lean predicate Hindman.FP.

  A finite family S is required to consist of subsets of the carrier. Its
  union covers Q1566341FP G A, and the conclusion keeps both the chosen
  member C of S and the new stream B internally existential. Exactly as in
  the indexed Lean declaration, the conclusion requires Q1566341FP G B to be
  contained in C; it does not add a separate containment in Q1566341FP G A.

  The definition below is a faithful abbreviation. The root artifact's final
  declaration is the single unproved $a corpus statement, and the root
  artifact adds no $p proof statement. The imported SetMM database retains
  its standard verified proofs.
$)

$c Q1566341FP $.

q1566341-fp-syntax $a class ( G Q1566341FP A ) $.

${
  $d A G f i j k x $.

  q1566341-fp-definition $a |- (
    G Q1566341FP A
  ) =
  { x e. ( Base ` G ) |
    E. k e. NN
      E. f e. ( NN0 ^m ( 0 ..^ k ) )
        (
          A. i e. ( 0 ..^ k )
            A. j e. ( 0 ..^ k )
              (
                i < j
                ->
                ( f ` i ) < ( f ` j )
              )
          /\
          ( G gsum ( A o. f ) ) = x
        )
  } $.
$}

${
  $d A B C G S $.

  thousand-theorems-q1566341-hindman $a |-
    A. G e. Smgrp
      A. A e. ( ( Base ` G ) ^m NN0 )
        A. S e. Fin
          (
            (
              S C_ ~P ( Base ` G )
              /\
              ( G Q1566341FP A ) C_ U. S
            )
            ->
            E. C e. S
              E. B e. ( ( Base ` G ) ^m NN0 )
                ( G Q1566341FP B ) C_ C
          )
  $.
$}
