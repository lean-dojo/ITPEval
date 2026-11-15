$(
  Statement-only formalization of Thousand Theorems corpus artifact Q4950096
  (thousand-theorems__metamath__Q4950096), "Bourbaki-Witt theorem": every
  inflationary endomap of a nonempty chain-complete partial order has a fixed
  point. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q4950096Chains(A,R) is the set of all nonempty subsets of A whose elements
  are pairwise comparable under R. Q4950096CCPO(A,R,S) says that R is a
  non-strict partial order on the nonempty carrier A and that S chooses, for
  every such chain, its least upper bound in A. Thus S renders exactly the
  cSup field and laws of the Lean ChainCompletePartialOrder structure.

  The final declaration is the single unproved corpus $a statement. It
  quantifies over arbitrary set-sized carriers and all structure fields, and
  its fixed point remains existentially quantified inside the conclusion.
$)

$c Q4950096Chains Q4950096CCPO $.

q4950096-chains-syntax $a class ( Q4950096Chains A R ) $.
q4950096-ccpo-syntax $a wff ( Q4950096CCPO A R S ) $.

$d A R c x y $.
q4950096-chains-definition $a |- (
  ( Q4950096Chains A R )
  =
  { c e. ~P A |
    (
      c =/= (/)
      /\
      A. x e. c A. y e. c ( x R y \/ y R x )
    )
  }
) $.

$d A R S c x y z $.
q4950096-ccpo-definition $a |- (
  ( Q4950096CCPO A R S )
  <->
  (
    A =/= (/)
    /\
    (
      R C_ ( A X. A )
      /\
      (
        A. x e. A x R x
        /\
        (
          A. x e. A A. y e. A A. z e. A
            ( ( x R y /\ y R z ) -> x R z )
          /\
          (
            A. x e. A A. y e. A
              ( ( x R y /\ y R x ) -> x = y )
            /\
            (
              S : ( Q4950096Chains A R ) --> A
              /\
              A. c e. ( Q4950096Chains A R )
                (
                  A. x e. c x R ( S ` c )
                  /\
                  A. z e. A
                    (
                      A. y e. c y R z
                      ->
                      ( S ` c ) R z
                    )
                )
            )
          )
        )
      )
    )
  )
) $.

$d a f r s x $.
thousand-theorems-q4950096-bourbaki-witt $a |-
  A. a A. r A. s A. f
    (
      (
        ( Q4950096CCPO a r s )
        /\
        (
          f : a --> a
          /\
          A. x e. a x r ( f ` x )
        )
      )
      ->
      E. x e. a ( f ` x ) = x
    )
$.
