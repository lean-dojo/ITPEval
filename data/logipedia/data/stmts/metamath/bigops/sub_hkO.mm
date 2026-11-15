$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sub_hkO, catalog title "bigops.sub_hkO": when the first natural
  bound is zero, the selected-index relation sub_hk holds. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain, and { 0 , 1 } is the Boolean
  carrier with true represented by 1. Full SetMM function spaces preserve the
  arbitrary natural-number maps, Boolean predicates, and natural-number-valued
  functions. LogSubHK unfolds the source sub_hk definition exactly; its final
  two function arguments remain explicit even though the source definition
  does not inspect them. Both declarations are unproved $a statement
  encodings; this database contains no $p proof declaration.
$)

$c LogSubHK $.

log-sub-hk-syntax $a wff ( LogSubHK h k a b p q f g ) $.

${
  $d a b f g h i k p q $.

  log-sub-hk-definition $a |- (
    ( LogSubHK h k a b p q f g )
    <->
    A. i e. NN0
      (
        i < a
        ->
        (
          ( p ` i ) = 1
          ->
          (
            (
              ( h ` i ) < b
              /\
              ( q ` ( h ` i ) ) = 1
            )
            /\
            ( k ` ( h ` i ) ) = i
          )
        )
      )
  ) $.
$}

${
  $d a b f g h k p q $.

  logipedia-bigops-sub-hko $a |-
    A. h e. ( NN0 ^m NN0 )
      A. k e. ( NN0 ^m NN0 )
        A. a e. NN0
          A. b e. NN0
            A. p e. ( { 0 , 1 } ^m NN0 )
              A. q e. ( { 0 , 1 } ^m NN0 )
                A. f e. ( NN0 ^m NN0 )
                  A. g e. ( NN0 ^m NN0 )
                    (
                      a = 0
                      ->
                      ( LogSubHK h k a b p q f g )
                    )
  $.
$}
