$(
  @{
    amc12a-2003-p24.0 @e |- ( ph -> A e. RR ) $@
    amc12a-2003-p24.1 @e |- ( ph -> B <_ A ) $@
    amc12a-2003-p24.2 @e |- ( ph -> B e. RR ) $@
    amc12a-2003-p24.3 @e |- ( ph -> 1 < B ) $@
    @( (Contributed by Stanislas Polu, 16-Nov-2020.) @)
    amc12a-2003-p24 @p |- ( ph ->
      ( E. a e. RR E. b e. RR
          ( ( 1 < b /\ b <_ a )
            /\ 0 = ( ( a logb ( a / b ) ) + ( b logb ( b / a ) ) ) )
        /\ ( ( A logb ( A / B ) ) + ( B logb ( B / A ) ) ) <_ 0 ) ) @=
      ? @.
  @}
$)
