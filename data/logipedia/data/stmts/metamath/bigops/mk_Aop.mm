$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.mk_Aop, catalog title "bigops.mk_Aop": an associative binary
  operation with a two-sided identity entails the source opaque Aop property
  for that identity element. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier h remains arbitrary, x is the source element nil, and the full
  SetMM function space ( ( h ^m h ) ^m h ) encodes the source curried
  operation h -> h -> h. LogAop h x is the source primitive proposition
  Aop h x; it is intentionally left opaque because the source module declares
  Aop as a constant without a definition. The three nested implications
  preserve the source left-identity, right-identity, and associativity
  assumptions and their quantifier scopes. Both declarations are unproved $a
  statement encodings; this database contains no $p proof declaration.
$)

$c LogAop $.

log-aop-syntax $a wff ( LogAop h x ) $.

${
  $d a b c h o x $.

  logipedia-bigops-mk-aop $a |-
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
                ( LogAop h x )
              )
            )
          )
  $.
$}
