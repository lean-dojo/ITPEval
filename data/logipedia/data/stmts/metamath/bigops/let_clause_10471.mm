$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.let_clause_10471, catalog title "bigops.let_clause_10471": a nested
  proposition about Boolean-selected natural-number products and mutually
  inverse selected-index maps, concluding the natural-number
  quotient-remainder identity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain, and {0,1} is the Boolean carrier
  with true represented by 1. LogSame, LogSubHK, and LogIso unfold the source
  selected-value condition, sub_hk predicate, and iso predicate exactly.
  LogNatBigop is the source bigop specialized to base 1 and natural
  multiplication, represented by the finite product over selected indices
  below its bound. LogNatDiv and LogNatMod totalize SetMM's positive-divisor
  operations exactly as in the source: division of x by zero is x + 1 and
  remainder modulo zero is x.
  All declarations are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c LogSame LogSubHK LogIso LogNatBigop LogNatDiv LogNatMod $.

log-same-syntax $a wff ( LogSame h a p f g ) $.
log-sub-hk-syntax $a wff ( LogSubHK h k a b p q f g ) $.
log-iso-syntax $a wff ( LogIso a b p q f g ) $.
log-nat-bigop-syntax $a class ( LogNatBigop m p f ) $.
log-nat-div-syntax $a class ( LogNatDiv x y ) $.
log-nat-mod-syntax $a class ( LogNatMod x y ) $.

${
  $d a f g h i p $.

  log-same-definition $a |- (
    ( LogSame h a p f g )
    <->
    A. i e. NN0
      (
        i < a
        ->
        (
          ( p ` i ) = 1
          ->
          ( f ` i ) = ( g ` ( h ` i ) )
        )
      )
  ) $.
$}

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

  log-iso-definition $a |- (
    ( LogIso a b p q f g )
    <->
    E. h e. ( NN0 ^m NN0 )
      E. k e. ( NN0 ^m NN0 )
        (
          (
            ( LogSame h a p f g )
            /\
            ( LogSubHK h k a b p q f g )
          )
          /\
          ( LogSubHK k h b a q p g f )
        )
  ) $.
$}

${
  $d f i m p $.

  log-nat-bigop-definition $a |- (
    ( LogNatBigop m p f )
    =
    prod_ i e.
      {
        i e. ( 0 ..^ m )
        |
        ( p ` i ) = 1
      }
      ( f ` i )
  ) $.
$}

log-nat-div-definition $a |- (
  ( LogNatDiv x y )
  =
  if (
    y = 0 ,
    ( x + 1 ) ,
    ( |_ ` ( x / y ) )
  )
) $.

log-nat-mod-definition $a |- (
  ( LogNatMod x y )
  =
  if (
    y = 0 ,
    x ,
    ( x mod y )
  )
) $.

${
  $d a b f g h i k m p q r s x y $.

  logipedia-bigops-let-clause-10471 $a |-
    A. a e. NN0
      A. b e. NN0
        A. p e. ( { 0 , 1 } ^m NN0 )
          A. q e. ( { 0 , 1 } ^m NN0 )
            A. f e. ( NN0 ^m NN0 )
              A. g e. ( NN0 ^m NN0 )
                (
                  ( LogIso a b p q f g )
                  ->
                  A. h e. ( NN0 ^m NN0 )
                    (
                      E. k e. ( NN0 ^m NN0 )
                        (
                          (
                            ( LogSame h a p f g )
                            /\
                            ( LogSubHK h k a b p q f g )
                          )
                          /\
                          ( LogSubHK k h b a q p g f )
                        )
                      ->
                      A. k e. ( NN0 ^m NN0 )
                        (
                          (
                            (
                              ( LogSame h a p f g )
                              /\
                              ( LogSubHK h k a b p q f g )
                            )
                            /\
                            ( LogSubHK k h b a q p g f )
                          )
                          ->
                          (
                            (
                              ( LogSame h a p f g )
                              /\
                              ( LogSubHK h k a b p q f g )
                            )
                            ->
                            (
                              ( LogSame h a p f g )
                              ->
                              A. i e. NN0
                                A. m e. NN0
                                  (
                                    A. r e. ( { 0 , 1 } ^m NN0 )
                                      (
                                        0 <_ a
                                        ->
                                        (
                                          ( LogSubHK h k 0 m p r f g )
                                          ->
                                          (
                                            ( LogSubHK k h m 0 r p g f )
                                            ->
                                            (
                                              ( LogNatBigop 0 p f )
                                              =
                                              ( LogNatBigop m r g )
                                            )
                                          )
                                        )
                                      )
                                    ->
                                    A. s e. ( { 0 , 1 } ^m NN0 )
                                      (
                                        0 <_ a
                                        ->
                                        (
                                          ( LogSubHK h k 0 ( m + 1 ) p s f g )
                                          ->
                                          (
                                            ( LogSubHK k h ( m + 1 ) 0 s p g f )
                                            ->
                                            A. x e. NN0
                                              A. y e. NN0
                                                x
                                                =
                                                (
                                                  (
                                                    y
                                                    x.
                                                    ( LogNatDiv x y )
                                                  )
                                                  +
                                                  ( LogNatMod x y )
                                                )
                                          )
                                        )
                                      )
                                  )
                            )
                          )
                        )
                    )
                )
  $.
$}
