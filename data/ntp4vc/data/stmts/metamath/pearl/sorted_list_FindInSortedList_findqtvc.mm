$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sorted_list_FindInSortedList_findqtvc
  (ntp4vc__metamath__pearl/sorted_list_FindInSortedList_findqtvc):
  the sorted-list search verification condition preserves sortedness of the
  tail when recursion is taken and states that the Boolean search result is
  true exactly when the searched integer occurs in the input list.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM Word ZZ is exactly the type of arbitrary finite zero-based lists of
  integers. NTP4VCMem is list membership by an in-range index.
  NTP4VCSorted is the source nondecreasing List.Sorted relation, expressed
  equivalently by comparison at every increasing pair of valid indices.

  NTP4VCDestruct preserves the first source list match, including the nested
  implications and the inner match which identifies the matched tail.
  NTP4VCResultPremise preserves the second match and both nested Boolean
  conditionals. Booleans use the exact two-element carrier { 0, 1 }, with
  false = 0 and true = 1. NTP4VCFindVC retains the conjunction and the
  universally quantified Boolean result at its source-internal scope.

  Splitting the typed parameters and sortedness premise into scoped essential
  hypotheses is bidirectionally equivalent to the source curried theorem.
  Every auxiliary $a declaration is syntax or an explicit faithful
  definition. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCMem NTP4VCSorted NTP4VCDestruct
  NTP4VCResultPremise NTP4VCFindVC
$.

ntp4vc-mem-syntax
  $a wff ( NTP4VCMem A B ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A ) $.
ntp4vc-destruct-syntax
  $a wff ( NTP4VCDestruct A B ) $.
ntp4vc-result-premise-syntax
  $a wff ( NTP4VCResultPremise A B C ) $.
ntp4vc-find-vc-syntax
  $a wff ( NTP4VCFindVC A B ) $.

${
  $d i A B $.

  ntp4vc-mem-definition $a |- (
    NTP4VCMem A B
  ) <-> (
    E. i e. ( 0 ..^ ( # ` B ) )
      ( B ` i ) = A
  ) $.
$}

${
  $d i j A $.

  ntp4vc-sorted-definition $a |- (
    NTP4VCSorted A
  ) <-> (
    A e. Word ZZ
    /\
    A. i e. ZZ A. j e. ZZ
      (
        (
          0 <_ i
          /\
          (
            i < j
            /\
            j < ( # ` A )
          )
        )
        ->
        ( A ` i ) <_ ( A ` j )
      )
  ) $.
$}

${
  $d f r y z A B $.

  ntp4vc-destruct-definition $a |- (
    NTP4VCDestruct A B
  ) <-> (
    A = (/)
    \/
    E. y e. ZZ E. r e. Word ZZ
      (
        A = ( <" y "> ++ r )
        /\
        (
          B =/= y
          ->
          (
            y < B
            ->
            (
              (
                E. z e. ZZ E. f e. Word ZZ
                  (
                    A = ( <" z "> ++ f )
                    /\
                    f = r
                  )
              )
              /\
              ( NTP4VCSorted r )
            )
          )
        )
      )
  ) $.
$}

${
  $d r y A B C $.

  ntp4vc-result-premise-definition $a |- (
    NTP4VCResultPremise A B C
  ) <-> (
    (
      A = (/)
      /\
      C = 0
    )
    \/
    E. y e. ZZ E. r e. Word ZZ
      (
        A = ( <" y "> ++ r )
        /\
        C = if (
          B = y ,
          1 ,
          if (
            y < B ,
            if (
              ( NTP4VCMem B r ) ,
              1 ,
              0
            ) ,
            0
          )
        )
      )
  ) $.
$}

${
  $d c A B $.

  ntp4vc-find-vc-definition $a |- (
    NTP4VCFindVC A B
  ) <-> (
    ( NTP4VCDestruct A B )
    /\
    A. c e. { 0 , 1 }
      (
        ( NTP4VCResultPremise A B c )
        ->
        (
          c = 1
          <->
          ( NTP4VCMem B A )
        )
      )
  ) $.
$}

${
  $d i j A B $.

  $( Source theorem parameters: A=l and B=x, followed by fact0. $)

  ntp4vc-l-list $e |- A e. Word ZZ $.
  ntp4vc-x-integer $e |- B e. ZZ $.
  ntp4vc-fact0 $e |- ( NTP4VCSorted A ) $.

  ntp4vc-pearl-sorted-list-find-in-sorted-list-find-vc
    $a |- ( NTP4VCFindVC A B ) $.
$}
