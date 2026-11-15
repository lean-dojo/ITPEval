;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_126:
;; the least positive natural number satisfying the prescribed greatest-common-
;; divisor and least-common-multiple equations with 40 equals 8.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-126-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-126-gcd a (- b a)))
            (t
             (mathd-numbertheory-126-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-126-lcm (a b)
  (if (and (natp a) (natp b))
      (if (or (equal a 0) (equal b 0))
          0
        (/ (* a b)
           (mathd-numbertheory-126-gcd a b)))
    0))

;; A positive b with the required LCM is at most that LCM. Thus checking all
;; positive b through x*(x+3) is equivalent to the source universal condition.
(defun mathd-numbertheory-126-minimal-through-p (a x b)
  (declare (xargs :measure (nfix b)))
  (if (zp b)
      t
    (and
     (implies
      (and
       (equal (mathd-numbertheory-126-gcd b 40)
              (+ x 3))
       (equal (mathd-numbertheory-126-lcm b 40)
              (* x (+ x 3))))
      (<= a b))
     (mathd-numbertheory-126-minimal-through-p
      a x (- b 1)))))

(defun mathd-numbertheory-126-statement (x a)
  (implies
   (and
    (natp x)
    (natp a)
    (< 0 x)
    (< 0 a)
    (equal (mathd-numbertheory-126-gcd a 40)
           (+ x 3))
    (equal (mathd-numbertheory-126-lcm a 40)
           (* x (+ x 3)))
    (mathd-numbertheory-126-minimal-through-p
     a x (* x (+ x 3))))
   (equal a 8)))

(value-triple :itpeval-statement-checked)
:q
