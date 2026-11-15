$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/mergesort_list_OCamlMergesort_mergesortqtvc: the OCaml-style
  mergesort verification condition states that every returned list is sorted
  and is a permutation of the input, using the recursive prefix operation in
  the nontrivial branch. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt, R is its total preorder
  le, and Word U is exactly the type of arbitrary finite zero-based U-lists.
  S is the source inductive sorted predicate, represented as the least subset
  of Word U closed under its empty, singleton, and ordered-cons constructors.
  The source sorted_mem and sorted_append laws are retained explicitly.

  P is prefix1 at the theorem's selected Inhabited elt instance. It remains an
  arbitrary total function from an integer and a U-list to a U-list, subject
  only to the source zero and positive-cons equations over the full unbounded
  integer domain ZZ.

  NTP4VCPerm compares the occurrence count of every element of U; on finite
  words this is equivalent in both directions to List.Perm. The source
  let-bound n is replaced definitionally by the word length. Its
  proposition-valued conditional is represented by the equivalent exhaustive
  guarded disjunction, while the result list remains internally universally
  quantified. The final $a declaration is Metamath's native unproved statement
  encoding; every preceding $a is syntax or a faithful definition, and this
  database contains no $p proof declaration.
$)

$c NTP4VCPerm $.

ntp4vc-perm-syntax $a wff ( NTP4VCPerm A B C ) $.

${
  $d k v A B C $.

  ntp4vc-perm-definition $a |- (
    NTP4VCPerm A B C
  ) <->
  (
    (
      A e. Word C
      /\
      B e. Word C
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. v e. C
        (
          (
            # `
            { k e. ( 0 ..^ ( # ` A ) ) | ( A ` k ) = v }
          )
          =
          (
            # `
            { k e. ( 0 ..^ ( # ` B ) ) | ( B ` k ) = v }
          )
        )
    )
  ) $.
$}

${
  $d k l m q r t w x y z L P R S U $.

  $( Source arbitrary inhabited carrier elt and total preorder le. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-le-relation $e |- R C_ ( U X. U ) $.

  ntp4vc-le-reflexive $e |- A. x e. U
    <. x , x >. e. R $.

  ntp4vc-le-transitive $e |- A. x e. U A. y e. U A. z e. U
    (
      (
        <. x , y >. e. R
        /\
        <. y , z >. e. R
      )
      ->
      <. x , z >. e. R
    ) $.

  ntp4vc-le-total $e |- A. x e. U A. y e. U
    (
      <. x , y >. e. R
      \/
      <. y , x >. e. R
    ) $.

  $( Exact least fixed-point presentation of the source sorted predicate. $)
  ntp4vc-sorted-subset $e |- S C_ Word U $.

  ntp4vc-sorted-empty $e |- (/) e. S $.

  ntp4vc-sorted-singleton $e |- A. x e. U
    <" x "> e. S $.

  ntp4vc-sorted-ordered-cons $e |- A. x e. U A. y e. U
    A. t e. Word U
      (
        (
          <. x , y >. e. R
          /\
          ( <" y "> ++ t ) e. S
        )
        ->
        ( <" x "> ++ <" y "> ++ t ) e. S
      ) $.

  ntp4vc-sorted-structural-induction $e |- A. q e. ~P S
    (
      (
        (/) e. q
        /\
        (
          A. x e. U <" x "> e. q
          /\
          A. x e. U A. y e. U A. t e. Word U
            (
              (
                <. x , y >. e. R
                /\
                ( <" y "> ++ t ) e. q
              )
              ->
              ( <" x "> ++ <" y "> ++ t ) e. q
            )
        )
      )
      ->
      q = S
    ) $.

  $( The source sorted_mem and sorted_append characterization axioms. $)
  ntp4vc-sorted-mem $e |- A. w e. Word U A. x e. U
    (
      (
        (
          A. y e. U
            (
              y e. ran w
              ->
              <. x , y >. e. R
            )
          /\
          w e. S
        )
        <->
        ( <" x "> ++ w ) e. S
      )
    ) $.

  ntp4vc-sorted-append $e |- A. l e. Word U A. m e. Word U
    (
      (
        (
          l e. S
          /\
          (
            m e. S
            /\
            A. x e. U A. y e. U
              (
                (
                  x e. ran l
                  /\
                  y e. ran m
                )
                ->
                <. x , y >. e. R
              )
          )
        )
        <->
        ( l ++ m ) e. S
      )
    ) $.

  $( Source operation prefix1 and its complete displayed equations. $)
  ntp4vc-prefix-function
    $e |- P e. ( ( Word U ) ^m ( ZZ X. Word U ) ) $.

  ntp4vc-prefix-zero $e |- A. w e. Word U
    ( P ` <. 0 , w >. ) = (/) $.

  ntp4vc-prefix-positive-cons $e |- A. k e. ZZ A. x e. U
    A. t e. Word U
      (
        0 < k
        ->
        (
          P ` <. k , ( <" x "> ++ t ) >.
        )
        =
        (
          <" x "> ++ ( P ` <. ( k - 1 ) , t >. )
        )
      ) $.

  $( Source theorem parameter L=l. $)
  ntp4vc-l-word $e |- L e. Word U $.

  ntp4vc-pearl-mergesort-list-ocamlmergesort-mergesort-vc $a |- (
    (
      (
        -. ( # ` L ) < 2
        ->
        (
          2 <_ ( # ` L )
          /\
          ( # ` L ) <_ ( # ` L )
        )
      )
      /\
      A. r e. Word U
        (
          (
            (
              ( # ` L ) < 2
              /\
              r = L
            )
            \/
            (
              -. ( # ` L ) < 2
              /\
              (
                r e. S
                /\
                (
                  NTP4VCPerm
                    r
                    ( P ` <. ( # ` L ) , L >. )
                    U
                )
              )
            )
          )
          ->
          (
            r e. S
            /\
            ( NTP4VCPerm r L U )
          )
        )
    )
  ) $.
$}
