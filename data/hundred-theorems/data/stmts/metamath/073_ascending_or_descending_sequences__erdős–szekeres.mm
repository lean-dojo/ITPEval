$(
  Statement-only formalization of Hundred Theorems item 073, the
  Erdos-Szekeres monotone subsequence theorem.

  This reproduces set.mm theorem erdsze. F is an injective real sequence of
  length N; if (R-1)(S-1) < N, it has an increasing subsequence of length R or
  a decreasing subsequence of length S.
$)

$[ library/set.mm $]

${
  $d F s $.
  $d R s $.
  $d N s $.
  $d ph s $.
  $d S s $.

  hundred-theorems-073-length $e
    |- ( ph -> N e. NN )
  $.
  hundred-theorems-073-sequence $e
    |- ( ph -> F : ( 1 ... N ) -1-1-> RR )
  $.
  hundred-theorems-073-increasing-length $e
    |- ( ph -> R e. NN )
  $.
  hundred-theorems-073-decreasing-length $e
    |- ( ph -> S e. NN )
  $.
  hundred-theorems-073-size-bound $e
    |- ( ph -> ( ( R - 1 ) x. ( S - 1 ) ) < N )
  $.

  hundred-theorems-073-erdos-szekeres $a
    |- (
         ph
         ->
         E. s e. ~P ( 1 ... N )
           (
             (
               R <_ ( # ` s )
               /\
               ( F |` s ) Isom < , < ( s , ( F " s ) )
             )
             \/
             (
               S <_ ( # ` s )
               /\
               ( F |` s ) Isom < , `' < ( s , ( F " s ) )
             )
           )
       )
  $.
$}
