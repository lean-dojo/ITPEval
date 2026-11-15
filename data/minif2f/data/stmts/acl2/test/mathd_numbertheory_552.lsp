;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_552: the distinct gcd values of 12*x + 7 and
;; 5*x + 2 over the positive natural numbers have sum 12.
;; This file contains no proof.
;;
;; The source hypotheses uniquely determine f, g, and h on their positive
;; natural domain, so they are represented by the explicit gcd function below.
;; Every common divisor of 12*x + 7 and 5*x + 2 divides
;; 5*(12*x + 7) - 12*(5*x + 2) = 11. Thus each gcd is either 1 or 11, and
;; shifting x by 11 preserves whether both affine values are divisible by 11.
;; The gcd-value function therefore has period 11 on positive naturals.
;; Consequently its full distinct image is exactly the image at x = 1,...,11,
;; which the recursive list below represents without duplicates.

(in-package "ACL2")

(defun mathd-numbertheory-552-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-552-gcd a (- b a)))
            (t
             (mathd-numbertheory-552-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-552-value (x)
  (if (and (natp x) (< 0 x))
      (mathd-numbertheory-552-gcd
       (+ (* 12 x) 7)
       (+ (* 5 x) 2))
    0))

(defun mathd-numbertheory-552-insert (value values)
  (if (member-equal value values)
      values
    (cons value values)))

(defun mathd-numbertheory-552-image-through (remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (mathd-numbertheory-552-insert
     (mathd-numbertheory-552-value remaining)
     (mathd-numbertheory-552-image-through (- remaining 1)))))

(defun mathd-numbertheory-552-sum (values)
  (if (consp values)
      (+ (car values)
         (mathd-numbertheory-552-sum (cdr values)))
    0))

(defun mathd-numbertheory-552-statement ()
  (equal
   (mathd-numbertheory-552-sum
    (mathd-numbertheory-552-image-through 11))
   12))

(value-triple :itpeval-statement-checked)
:q
