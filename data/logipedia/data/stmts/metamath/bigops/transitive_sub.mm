$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.transitive_sub, catalog title "bigops.transitive_sub": selected-index
  sub_hk correspondences between natural-number bounds compose transitively.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain, and { 0 , 1 } is the Boolean
  carrier with true represented by 1. Full SetMM function spaces preserve all
  arbitrary natural-to-natural maps and Boolean predicates. LogSubHK unfolds
  the source relation exactly. LogComposedSubHK is its beta-reduced conclusion
  for the forward composition j(h(i)) and inverse composition k(l(j(h(i)))).
  The final function arguments remain explicit even though the source
  definition does not inspect them. All declarations are unproved $a
  statement encodings; this database contains no $p proof declaration.
$)

$c LogSubHK LogComposedSubHK $.

log-sub-hk-syntax $a wff ( LogSubHK h k a b p q f g ) $.

log-composed-sub-hk-syntax $a wff
  ( LogComposedSubHK h k j l a b p q f g ) $.

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
  $d a b f g h i j k l p q $.

  log-composed-sub-hk-definition $a |- (
    ( LogComposedSubHK h k j l a b p q f g )
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
              ( j ` ( h ` i ) ) < b
              /\
              ( q ` ( j ` ( h ` i ) ) ) = 1
            )
            /\
            ( k ` ( l ` ( j ` ( h ` i ) ) ) ) = i
          )
        )
      )
  ) $.
$}

${
  $d a b c e f g h j k l p q r $.

  logipedia-bigops-transitive-sub $a |-
    A. h e. ( NN0 ^m NN0 )
      A. k e. ( NN0 ^m NN0 )
        A. j e. ( NN0 ^m NN0 )
          A. l e. ( NN0 ^m NN0 )
            A. a e. NN0
              A. b e. NN0
                A. c e. NN0
                  A. p e. ( { 0 , 1 } ^m NN0 )
                    A. q e. ( { 0 , 1 } ^m NN0 )
                      A. r e. ( { 0 , 1 } ^m NN0 )
                        A. f e. ( NN0 ^m NN0 )
                          A. g e. ( NN0 ^m NN0 )
                            A. e e. ( NN0 ^m NN0 )
                              (
                                ( LogSubHK h k a b p q f g )
                                ->
                                (
                                  ( LogSubHK j l b c q r g e )
                                  ->
                                  (
                                    LogComposedSubHK
                                      h k j l a c p r f e
                                  )
                                )
                              )
  $.
$}
