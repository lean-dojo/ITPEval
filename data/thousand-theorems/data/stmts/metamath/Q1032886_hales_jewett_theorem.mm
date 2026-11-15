$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1032886
  (thousand-theorems__metamath__Q1032886), "Hales-Jewett theorem": for every
  finite alphabet and finite color set, some finite-dimensional word space
  has a monochromatic combinatorial line under every coloring. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A line is encoded by a nonempty subset V of the finite coordinate set I
  and a function B assigning fixed alphabet symbols on I \ V. For x in the
  alphabet, B u. ( V X. { x } ) is the corresponding word: it equals x on
  every variable coordinate and B elsewhere. This is bidirectionally
  equivalent to the source Line structure's Option-valued idxFun and proper
  field, including for empty alphabets.

  The final declaration is the single unproved $a corpus statement. This
  database contains no $p proof statement.
$)

${
  $d A B C I K V c x $.

  thousand-theorems-q1032886-hales-jewett $a |-
    A. A e. Fin
      A. K e. Fin
        E. I e. Fin
          A. C
            (
              C : ( A ^m I ) --> K
              ->
              E. V e. ( ~P I \ { (/) } )
                E. B e. ( A ^m ( I \ V ) )
                  E. c e. K
                    A. x e. A
                      ( C ` ( B u. ( V X. { x } ) ) ) = c
            )
  $.
$}
