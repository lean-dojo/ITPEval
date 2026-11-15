(*
  Authors: Albert Qiaochu Jiang
*)

theory algebra_sqineq_2unitcircatblt1 imports
Complex_Main

begin

theorem algebra_sqineq_2unitcircatblt1:
  fixes a b :: real
  assumes "a^2 + b^2 = 2"
  shows "a * b <= 1"
  by sorry


end