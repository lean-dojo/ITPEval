$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.mk_ACop, catalog title "bigops.mk_ACop": a carrier element has the
  opaque ACop property when a binary operation on the carrier has that
  element as a two-sided identity and is associative and commutative.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier h remains arbitrary, x is the source element nil, and the full
  SetMM function space ( ( h ^m h ) ^m h ) encodes the source curried
  operation h -> h -> h. LogACop h x is the source primitive proposition
  ACop h x; it is intentionally left opaque because the source module
  declares ACop as a constant without a definition. The four nested
  implications preserve the source identity, associativity, and commutativity
  assumptions and their quantifier scopes. Both declarations are unproved $a
  statement encodings; this database contains no $p proof declaration.
$)

$c LogACop $.

log-acop-syntax $a wff ( LogACop h x ) $.

${
  $d a b c h o x $.

  logipedia-bigops-mk-acop $a |-
    A. h
      A. x e. h
        A. o e. ( ( h ^m h ) ^m h )
          (
            A. a e. h ( ( o ` x ) ` a ) = a
            ->
            (
              A. a e. h ( ( o ` a ) ` x ) = a
              ->
              (
                A. a e. h
                  A. b e. h
                    A. c e. h
                      (
                        ( o ` a ) ` ( ( o ` b ) ` c )
                      )
                      =
                      (
                        ( o ` ( ( o ` a ) ` b ) ) ` c
                      )
                ->
                (
                  A. a e. h
                    A. b e. h
                      ( ( o ` a ) ` b ) = ( ( o ` b ) ` a )
                  ->
                  ( LogACop h x )
                )
              )
            )
          )
  $.
$}
