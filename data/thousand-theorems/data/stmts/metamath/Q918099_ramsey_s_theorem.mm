$(
  Statement-only formalization of Thousand Theorems corpus artifact Q918099
  (thousand-theorems__metamath__Q918099), "Ramsey's theorem": every coloring
  of the r-element subsets of an infinite set of natural numbers by a finite
  palette has an infinite monochromatic subset. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary Lean type alpha is represented by a set A, and the finset K
  is represented by a finite subset of A. The coloring C is a total function
  from all finite subsets of NN0 to A, while its palette condition is imposed
  only on the r-element finite subsets of M.

  The class { x e. ( ~P M i^i Fin ) | ( # ` x ) = r } is exactly the source
  rset' r M: its members are the finite subsets of M having cardinality r.
  Non-membership in Fin expresses infinitude. Thus the witnesses N and c are
  internally existential, N is an infinite subset of M, c belongs to K, and
  every r-element subset of N has color c.

  The following declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A C K M N c e r x $.

  thousand-theorems-q918099-ramsey-r $a |-
    A. A e. _V
      A. K e. ( ~P A i^i Fin )
        A. r e. NN0
          A. M e. ~P NN0
            A. C
              (
                (
                  (
                    -. M e. Fin
                    /\
                    C : ( ~P NN0 i^i Fin ) --> A
                  )
                  /\
                  A. e e.
                    { x e. ( ~P M i^i Fin ) | ( # ` x ) = r }
                    ( C ` e ) e. K
                )
                ->
                E. N e. ~P M
                  (
                    -. N e. Fin
                    /\
                    E. c e. K
                      A. e e.
                        { x e. ( ~P N i^i Fin ) | ( # ` x ) = r }
                        ( C ` e ) = c
                  )
              )
  $.
$}
