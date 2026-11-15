;; Statement-only formalization of miniF2F corpus artifact imo_1988_p6:
;; for positive natural numbers a and b, if a*b+1 divides a^2+b^2, then
;; their quotient is the square of a natural number. This file contains no
;; proof.

(in-package "ACL2")

;; Since a*b+1 is positive, the quotient is nonnegative and no greater than
;; the numerator. Thus searching from the numerator down to zero is equivalent
;; to the source existential quantifier over all natural square roots.
(defun imo-1988-p6-square-witness-through-p (quotient candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (natp candidate)
      (or (equal (* candidate candidate) quotient)
          (and (not (zp candidate))
               (imo-1988-p6-square-witness-through-p
                quotient (- candidate 1))))
    nil))

(defun imo-1988-p6-statement (a b)
  (let* ((denominator (+ (* a b) 1))
         (numerator (+ (* a a) (* b b))))
    (implies
     (and (natp a)
          (natp b)
          (< 0 a)
          (< 0 b)
          (equal (mod numerator denominator) 0))
     (imo-1988-p6-square-witness-through-p
      (/ numerator denominator)
      numerator))))

(value-triple :itpeval-statement-checked)
:q
