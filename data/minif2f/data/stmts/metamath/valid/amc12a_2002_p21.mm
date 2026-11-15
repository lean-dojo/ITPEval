$(
  @{
    amc12a-2002-p21.0 @e |- ( ph -> U : NN0 --> NN0 ) $@
    amc12a-2002-p21.1 @e |- ( ph -> ( U ` 0 ) = 4 ) $@
    amc12a-2002-p21.2 @e |- ( ph -> ( U ` 1 ) = 7 ) $@
    amc12a-2002-p21.3 @e |- ( ph -> A. n e. NN0
      ( U ` ( n + 2 ) ) = ( ( ( U ` n ) + ( U ` ( n + 1 ) ) ) mod ; 1 0 ) ) $@
    @( (Contributed by Kunhao Zheng, 4-May-2021.) @)
    amc12a-2002-p21 @p |- ( ph -> A. n e. NN0
      ( sum_ k e. ( 0 ..^ n ) ( U ` k ) > ; ; ; ; 1 0 0 0 0
        -> ; ; ; 1 9 9 9 <_ n ) ) @=
      ? @.
  @}
$)
