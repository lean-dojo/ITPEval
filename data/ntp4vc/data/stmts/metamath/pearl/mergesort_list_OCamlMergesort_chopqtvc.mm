$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/mergesort_list_OCamlMergesort_chopqtvc: the list-chopping
  verification condition establishes progress for a positive prefix length
  and reconstructs the original list from that prefix and the returned
  suffix. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier alpha, represented by a
  nonempty set, and Word U is exactly the type of arbitrary finite
  zero-based U-lists. P is the source prefix1 operation at the theorem's
  selected Inhabited instance, represented as a total function from an
  integer and a word to a word. Its two scoped equations are exactly
  prefix_def1 and prefix_def2 over the full unbounded integer domain ZZ.

  N and L are the source theorem parameters n and l. Source list matches are
  expanded into internal existential head-tail decompositions; the empty
  branches remain false. The let-bound o1 is replaced definitionally by
  N - 1, and the proposition-valued conditional is rendered by its two
  exhaustive guarded branches. Thus no match witness is moved to an external
  parameter, and every result quantifier retains its original scope.

  The final $a declaration is Metamath's native unproved statement encoding;
  every preceding $e declaration is a source type, definition equation, or
  explicit theorem assumption. This database contains no $p declaration.
$)

${
  $d k r t w x L N P U $.

  $( Source arbitrary inhabited carrier alpha. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.

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

  $( Source theorem parameters N=n and L=l, followed by fact0 and fact1. $)
  ntp4vc-n-integer $e |- N e. ZZ $.
  ntp4vc-l-word $e |- L e. Word U $.
  ntp4vc-fact0 $e |- 0 <_ N $.
  ntp4vc-fact1 $e |- N <_ ( # ` L ) $.

  ntp4vc-pearl-mergesort-list-ocamlmergesort-chop-vc $a |- (
    (
      N =/= 0
      ->
      E. x e. U E. t e. Word U
        (
          L = ( <" x "> ++ t )
          /\
          (
            (
              0 <_ N
              /\
              ( N - 1 ) < N
            )
            /\
            (
              0 <_ ( N - 1 )
              /\
              ( N - 1 ) <_ ( # ` t )
            )
          )
        )
    )
    /\
    A. r e. Word U
      (
        (
          (
            N = 0
            /\
            r = L
          )
          \/
          (
            N =/= 0
            /\
            E. x e. U E. t e. Word U
              (
                L = ( <" x "> ++ t )
                /\
                t = (
                  ( P ` <. ( N - 1 ) , t >. )
                  ++
                  r
                )
              )
          )
        )
        ->
        L = (
          ( P ` <. N , L >. )
          ++
          r
        )
      )
  ) $.
$}
