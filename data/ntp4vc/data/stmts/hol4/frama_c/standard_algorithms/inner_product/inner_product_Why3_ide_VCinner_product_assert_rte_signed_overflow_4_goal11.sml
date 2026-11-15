(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/inner_product/inner_product_Why3_ide_VCinner_product_assert_rte_signed_overflow_4_goal11:
  signed 32-bit upper-bound overflow safety for the next inner-product
  accumulation step under the modeled value and memory bounds. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal11 =
  ``let inner_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let inner_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let inner_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let inner_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let inner_unchanged =
      \mint_0 : (int # int) -> int.
       \mint_1 : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint_1 (inner_shift a j) = mint_0 (inner_shift a j)
    in
    let inner_productbounds =
      \mint : (int # int) -> int.
       \a : int # int. \b : int # int. \n : int.
        !j : int.
          let y = mint (inner_shift a j) * mint (inner_shift b j) in
            0 <= j ==>
            j < n ==>
            -2147483648 <= y /\ y <= 2147483647
    in
    let inner_innerproductbounds =
      \l_innerproduct :
        ((int # int) -> int) ->
        (int # int) -> (int # int) -> int -> int -> int.
       \mint : (int # int) -> int.
       \a : int # int. \b : int # int. \n : int. \init : int.
        !j : int.
          let y = l_innerproduct mint a b j init in
            j <= n ==>
            0 <= j ==>
            -2147483648 <= y /\ y <= 2147483647
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !to_sint32 : int -> int.
      !l_innerproduct :
        ((int # int) -> int) ->
        (int # int) -> (int # int) -> int -> int -> int.
        (!z : int. inner_is_sint32 (to_sint32 z)) ==>
        (!z : int.
          inner_is_sint32 z ==>
          to_sint32 z = z) ==>
        (!n init : int.
         !mint : (int # int) -> int.
         !a b : int # int.
          n <= 0 ==>
          inner_is_sint32 init ==>
          l_innerproduct mint a b n init = init) ==>
        (!n init : int.
         !mint : (int # int) -> int.
         !a b : int # int.
          0 < n ==>
          inner_is_sint32 init ==>
          l_innerproduct mint a b (n - 1) init +
            mint (inner_shift a (n - 1)) * mint (inner_shift b (n - 1)) =
          l_innerproduct mint a b n init) ==>
        (!init : int.
         !mint_0 mint_1 : (int # int) -> int.
         !a : int # int.
         !n : int.
         !b : int # int.
          inner_is_sint32 init ==>
          inner_unchanged mint_0 mint_1 a 0 n ==>
          inner_unchanged mint_0 mint_1 b 0 n ==>
          l_innerproduct mint_1 a b n init =
          l_innerproduct mint_0 a b n init) ==>
        !t_1 : (int # int) -> int.
        !a : int # int.
        !i_2 : int.
        !a_1 : int # int.
        !i_1 i : int.
        !t : int -> int.
          let x = t_1 (inner_shift a i_2) in
          let x_1 = t_1 (inner_shift a_1 i_2) in
          let x_2 = l_innerproduct t_1 a_1 a i_2 i_1 in
            i_2 <= i ==>
            0 <= i_2 ==>
            i_2 < i ==>
            region (FST a) <= 0 ==>
            region (FST a_1) <= 0 ==>
            linked t ==>
            inner_is_uint32 i ==>
            inner_is_uint32 i_2 ==>
            inner_is_sint32 i_1 ==>
            inner_productbounds t_1 a_1 a i ==>
            inner_is_sint32 x ==>
            inner_is_sint32 x_1 ==>
            inner_innerproductbounds l_innerproduct t_1 a_1 a i i_1 ==>
            inner_valid_rd t (inner_shift a 0) i ==>
            inner_valid_rd t (inner_shift a_1 0) i ==>
            inner_is_sint32 x_2 ==>
            x_2 + to_sint32 (x * x_1) <= 2147483647``;
