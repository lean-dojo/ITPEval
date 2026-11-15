$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_fast_sizeqtvc: the Braun-tree fast-size
  verification condition exposes the recursive subtree size bounds and shows
  that the fast arithmetic decomposition equals the recursive tree size.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt. T is exactly the source
  inductive binary-tree carrier: NTP4VCEmpty and NTP4VCNode give disjoint
  injective tagged constructors, while constructor closure, exhaustiveness,
  and structural induction rule out both missing finite trees and extraneous
  non-well-founded values.

  S and I represent the source integer-valued size function and Braun
  invariant. Their equations below are the complete recursive definitions
  over T and the full integer domain ZZ, so the externally named operations
  are uniquely determined by structural recursion and add no mathematical
  premise beyond the source definitions.

  Each source tree match is expanded into its disjoint Empty and Node cases.
  In the Node branch, the nested match on the same tree becomes the source
  disjunction l = r or r = r. The let-bound m is replaced by S applied to the
  right subtree, the offset o1 remains existentially quantified inside the
  result antecedent, and result retains its universal integer scope. The
  final $a declaration is Metamath's native unproved statement encoding; this
  database contains no $p proof declaration.
$)

$c NTP4VCEmpty NTP4VCNode $.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C ) $.

ntp4vc-empty-def $a |- NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-node-def $a |- ( NTP4VCNode A B C ) =
  <. 1 , <. A , <. B , C >. >. >. $.

${
  $d e l o q r s t u v x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source inhabited carrier elt. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.

  $( Exact finite inductive binary-tree carrier over U. $)
  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. l e. T A. y e. U A. r e. T
    ( NTP4VCNode l y r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. l e. T E. y e. U E. r e. T
        t = ( NTP4VCNode l y r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCEmpty e. s
        /\
        A. l e. T A. y e. U A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCNode l y r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Types of the two source recursive definitions used by the VC. $)
  ntp4vc-size-function $e |- S e. ( ZZ ^m T ) $.
  ntp4vc-inv-predicate $e |- I C_ T $.

  $( Integer-valued size equations. $)
  ntp4vc-size-empty $e |- ( S ` NTP4VCEmpty ) = 0 $.

  ntp4vc-size-node $e |- A. l e. T A. y e. U A. r e. T
    (
      S ` ( NTP4VCNode l y r )
    )
    =
    (
      ( 1 + ( S ` l ) )
      +
      ( S ` r )
    ) $.

  $( Braun invariant equations. $)
  ntp4vc-inv-empty $e |- NTP4VCEmpty e. I $.

  ntp4vc-inv-node $e |- A. l e. T A. y e. U A. r e. T
    (
      ( NTP4VCNode l y r ) e. I
      <->
      (
        (
          ( S ` l ) = ( S ` r )
          \/
          ( S ` l ) = ( ( S ` r ) + 1 )
        )
        /\
        (
          l e. I
          /\
          r e. I
        )
      )
    ) $.

  $( Source theorem parameter A=t, followed by fact0. $)
  ntp4vc-t-tree $e |- A e. T $.
  ntp4vc-fact0 $e |- A e. I $.

  ntp4vc-pearl-braun-trees-braun-heaps-fast-size-vc $a |- (
    (
      A = NTP4VCEmpty
      \/
      E. l e. T E. y e. U E. r e. T
        (
          A = ( NTP4VCNode l y r )
          /\
          (
            (
              (
                l = r
                \/
                r = r
              )
              /\
              r e. I
            )
            /\
            (
              l e. I
              /\
              (
                0 <_ ( S ` r )
                /\
                (
                  ( S ` r ) <_ ( S ` l )
                  /\
                  ( S ` l ) <_ ( ( S ` r ) + 1 )
                )
              )
            )
          )
        )
    )
    /\
    A. q e. ZZ
      (
        (
          (
            A = NTP4VCEmpty
            /\
            q = 0
          )
          \/
          E. l e. T E. y e. U E. r e. T
            (
              A = ( NTP4VCNode l y r )
              /\
              E. o e. ZZ
                (
                  ( S ` l ) = ( ( S ` r ) + o )
                  /\
                  q =
                    (
                      ( 1 + ( 2 x. ( S ` r ) ) )
                      +
                      o
                    )
                )
            )
        )
        ->
        q = ( S ` A )
      )
  ) $.
$}
