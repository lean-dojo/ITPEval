$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sub0_to_false, catalog title "bigops.sub0_to_false": a zero target
  bound in the selected-index sub_hk relation forces the source Boolean
  predicate to be false at every index below its bound. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain, and { 0 , 1 } is the Boolean
  carrier with true represented by 1 and false by 0. Full SetMM function
  spaces preserve the arbitrary natural-number maps, Boolean predicates, and
  natural-number-valued functions. LogSubHK unfolds the source sub_hk
  definition exactly; its final two function arguments remain explicit even
  though the source definition does not inspect them. All declarations are
  unproved $a statement encodings; this database contains no $p proof
  declaration.
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
  $d a b f g h i k p q $.

  logipedia-bigops-sub0-to-false $a |-
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
                      (
                        ( LogSubHK h k b a q p g f )
                        ->
                        A. i e. NN0
                          (
                            i < b
                            ->
                            ( q ` i ) = 0
                          )
                      )
                    )
  $.
$}
