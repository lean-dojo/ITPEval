$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1097021
  (thousand-theorems__metamath__Q1097021), "Minkowski's theorem": a convex
  symmetric subset of a finite-dimensional real normed vector space whose
  Haar measure exceeds two to the dimension times a lattice fundamental
  domain's measure contains a nonzero point of the lattice. This file contains
  no proof of its own.
$)

$[ lib/set.mm $]

$(
  V ranges over arbitrary SetMM normed vector spaces over RRfld, including the
  zero-dimensional space. M is a measure on the Borel sigma-algebra generated
  by V's norm topology. Q1097021Haar expands the source IsAddHaarMeasure
  assumptions: translation invariance, finite measure on compact sets, and
  positive measure on nonempty open sets.

  Q1097021Measure uses the outer measure canonically induced by the SetMM
  Borel measure, so it evaluates arbitrary subsets just as Lean's measure
  does; *e is SetMM's extended-real multiplication used in the volume
  inequality. Q1097021Null and Q1097021NullMeasurable render measure-null and
  null-measurable sets. Q1097021Fundamental expands IsAddFundamentalDomain:
  the domain is null-measurable, almost every point has a translate by L in
  the domain, and distinct L-translates of the domain are almost everywhere
  disjoint. Q1097021Convex and Q1097021Symmetric use V's native real scalar,
  addition, and inverse operations.

  The final declaration is the single unproved corpus $a statement. All
  preceding root-file $a declarations are syntax or faithful definitions.
  This root artifact contributes no $p statement; the included SetMM library
  contains its standard verified proofs.
$)

$c Q1097021Translate Q1097021Measure Q1097021Null
   Q1097021NullMeasurable Q1097021Haar Q1097021Fundamental
   Q1097021Symmetric Q1097021Convex $.

q1097021-translate-syntax $a class ( Q1097021Translate V a A ) $.
q1097021-measure-syntax $a class ( Q1097021Measure M A ) $.
q1097021-null-syntax $a wff ( Q1097021Null M A ) $.
q1097021-null-measurable-syntax
  $a wff ( Q1097021NullMeasurable M A ) $.
q1097021-haar-syntax $a wff ( Q1097021Haar V M ) $.
q1097021-fundamental-syntax
  $a wff ( Q1097021Fundamental V M L F ) $.
q1097021-symmetric-syntax $a wff ( Q1097021Symmetric V S ) $.
q1097021-convex-syntax $a wff ( Q1097021Convex V S ) $.

${
  $d A V a x y $.

  q1097021-translate-definition $a |- (
    Q1097021Translate V a A
  ) = {
    y e. ( Base ` V ) |
      E. x e. A y = ( a ( +g ` V ) x )
  } $.
$}

${
  $d A M $.

  q1097021-measure-definition $a |- (
    Q1097021Measure M A
  ) = ( ( toOMeas ` M ) ` A ) $.
$}

${
  $d A M $.

  q1097021-null-definition $a |- (
    ( Q1097021Null M A )
    <->
    ( Q1097021Measure M A ) = 0
  ) $.
$}

${
  $d A M b $.

  q1097021-null-measurable-definition $a |- (
    ( Q1097021NullMeasurable M A )
    <->
    E. b e. dom M
      (
        Q1097021Null
        M
        ( ( A \ b ) u. ( b \ A ) )
      )
  ) $.
$}

${
  $d M V a b k u $.

  q1097021-haar-definition $a |- (
    ( Q1097021Haar V M )
    <->
    (
      M e.
        (
          measures
          `
          ( sigaGen ` ( TopOpen ` V ) )
        )
      /\
      (
        A. a e. ( Base ` V ) A. b e. ~P ( Base ` V )
          (
            ( Q1097021Measure M ( Q1097021Translate V a b ) )
            =
            ( Q1097021Measure M b )
          )
        /\
        (
          A. k e. ~P ( Base ` V )
            (
              (
                ( ( TopOpen ` V ) |`t k ) e. Comp
                ->
                ( Q1097021Measure M k ) e. ( 0 [,) +oo )
              )
            )
          /\
          A. u e. ( TopOpen ` V )
            (
              u =/= (/)
              ->
              0 < ( Q1097021Measure M u )
            )
        )
      )
    )
  ) $.
$}

${
  $d F L M V a b x $.

  q1097021-fundamental-definition $a |- (
    ( Q1097021Fundamental V M L F )
    <->
    (
      ( Q1097021NullMeasurable M F )
      /\
      (
        (
          Q1097021Null
          M
          {
            x e. ( Base ` V ) |
              -. E. a e. L
                ( a ( +g ` V ) x ) e. F
          }
        )
        /\
        A. a e. L A. b e. L
          (
            a =/= b
            ->
            (
              Q1097021Null
              M
              (
                ( Q1097021Translate V a F )
                i^i
                ( Q1097021Translate V b F )
              )
            )
          )
      )
    )
  ) $.
$}

${
  $d S V x $.

  q1097021-symmetric-definition $a |- (
    ( Q1097021Symmetric V S )
    <->
    A. x e. S
      ( ( -g ` V ) ` x ) e. S
  ) $.
$}

${
  $d S V t x y $.

  q1097021-convex-definition $a |- (
    ( Q1097021Convex V S )
    <->
    A. x e. S A. y e. S A. t e. ( 0 [,] 1 )
      (
        (
          ( t ( .s ` V ) x )
          ( +g ` V )
          ( ( 1 - t ) ( .s ` V ) y )
        )
        e. S
      )
  ) $.
$}

${
  $d f l m s v w x $.

  thousand-theorems-q1097021-minkowski $a |-
    A. w e. { v e. NrmVec | ( Scalar ` v ) = RRfld }
      A. m A. l A. f A. s
        (
          (
            (
              ( dim ` w ) e. NN0
              /\
              ( Q1097021Haar w m )
            )
            /\
            (
              (
                l e. ( SubGrp ` w )
                /\
                l ~<_ _om
              )
              /\
              (
                f e. ~P ( Base ` w )
                /\
                s e. ~P ( Base ` w )
              )
            )
          )
          ->
          (
            (
              (
                ( Q1097021Fundamental w m l f )
                /\
                (
                  ( Q1097021Symmetric w s )
                  /\
                  ( Q1097021Convex w s )
                )
              )
              /\
              (
                (
                  ( Q1097021Measure m f )
                  *e
                  ( 2 ^ ( dim ` w ) )
                )
                <
                ( Q1097021Measure m s )
              )
            )
            ->
            (
              E. x e. l
                (
                  x =/= ( 0g ` w )
                  /\
                  x e. s
                )
            )
          )
        )
  $.
$}
