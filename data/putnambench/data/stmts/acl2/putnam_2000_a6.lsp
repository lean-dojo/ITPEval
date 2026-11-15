;; Statement-only formalization of PutnamBench corpus artifact putnam_2000_a6:
;; an integer-polynomial orbit starting at zero can return to zero at a
;; positive time only if its first or second iterate is zero. This file
;; contains no proof.

(in-package "ACL2")

;; A polynomial in Z[x] is represented uniquely by its finite list of
;; coefficients in ascending degree order. NIL represents the zero polynomial,
;; and a nonzero polynomial has a nonzero final coefficient.
(defun putnam-2000-a6-integer-list-p (values)
  (if (consp values)
      (and (integerp (car values))
           (putnam-2000-a6-integer-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2000-a6-integer-polynomial-p (coefficients)
  (and
   (putnam-2000-a6-integer-list-p coefficients)
   (or (endp coefficients)
       (not (equal (car (last coefficients)) 0)))))

;; Horner evaluation is definitionally evaluation of the represented
;; integer-coefficient polynomial.
(defun putnam-2000-a6-polynomial-evaluate (coefficients value)
  (if (consp coefficients)
      (+ (car coefficients)
         (* value
            (putnam-2000-a6-polynomial-evaluate
             (cdr coefficients) value)))
    0))

;; This is the unique sequence satisfying a_0 = 0 and
;; a_(n+1) = f(a_n), so the source sequence parameter and its recurrence
;; assumptions are eliminated definitionally.
(defun putnam-2000-a6-iterate (coefficients steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      0
    (putnam-2000-a6-polynomial-evaluate
     coefficients
     (putnam-2000-a6-iterate coefficients (- steps 1)))))

;; Since the conclusion is independent of m,
;;
;;   (exists m > 0, a_m = 0) -> Q
;;
;; is bidirectionally equivalent to the pointwise universal form
;;
;;   forall m > 0, a_m = 0 -> Q.
;;
;; ACL2 implicitly universally quantifies the arguments of this predicate.
(defun putnambench-putnam-2000-a6-statement (coefficients m)
  (implies
   (and
    (putnam-2000-a6-integer-polynomial-p coefficients)
    (natp m)
    (< 0 m)
    (equal
     (putnam-2000-a6-iterate coefficients m)
     0))
   (or
    (equal
     (putnam-2000-a6-iterate coefficients 1)
     0)
    (equal
     (putnam-2000-a6-iterate coefficients 2)
     0))))

(value-triple :itpeval-statement-checked)
:q
