;; Statement-only formalization of miniF2F corpus artifact amc12b_2020_p6:
;; for every natural n at least 9, the factorial quotient
;; ((n + 2)! - (n + 1)!)/n! is the square of a natural number. This file
;; contains no proof.

(in-package "ACL2")

(defun amc12b-2020-p6-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (amc12b-2020-p6-factorial (- n 1)))))

;; If x^2 is the displayed quotient, then x is no larger than its natural
;; numerator because n! is positive. Thus this finite search is equivalent to
;; the source existential over all natural x.
(defun amc12b-2020-p6-square-witness-through-p (radicand x)
  (declare (xargs :measure (nfix x)))
  (if (natp x)
      (or (equal (* x x) radicand)
          (and (not (zp x))
               (amc12b-2020-p6-square-witness-through-p
                radicand (- x 1))))
    nil))

(defun amc12b-2020-p6-statement (n)
  (implies
   (and (natp n)
        (<= 9 n))
   (let* ((factorial-n
           (amc12b-2020-p6-factorial n))
          (factorial-n-plus-one
           (amc12b-2020-p6-factorial (+ n 1)))
          (factorial-n-plus-two
           (amc12b-2020-p6-factorial (+ n 2)))
          (numerator
           (- factorial-n-plus-two factorial-n-plus-one))
          (radicand
           (/ numerator factorial-n)))
     (amc12b-2020-p6-square-witness-through-p
      radicand numerator))))

(value-triple :itpeval-statement-checked)
:q
