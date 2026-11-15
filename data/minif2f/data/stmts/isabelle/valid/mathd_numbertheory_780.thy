(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_numbertheory_780 imports
Complex_Main

begin

theorem mathd_numbertheory_780:
  fixes m x :: int
  assumes h0 : "0 \<le> x"
    and h1 : "10 \<le> m"
    and h2 : "m \<le> 99"
    and h3 : "(6 * x) mod m = 1"
    and h4 : "(x - 6^2) mod m = 0"
  shows "m = 43"
  by sorry

end
