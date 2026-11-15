;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_629: 18 is the least positive natural number t such
;; that lcm(12,t)^3 = (12*t)^2. This file contains no proof.
;;
;; Since 18 itself is required to satisfy the predicate, checking that no
;; natural below 18 satisfies it is bidirectionally equivalent to the source
;; universal minimality condition.

(in-package "ACL2")

(defun mathd-numbertheory-629-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-629-gcd a (- b a)))
            (t
             (mathd-numbertheory-629-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-629-lcm (a b)
  (if (and (posp a) (posp b))
      (/ (* a b)
         (mathd-numbertheory-629-gcd a b))
    0))

(defun mathd-numbertheory-629-solution-p (t-value)
  (and (natp t-value)
       (< 0 t-value)
       (equal
        (expt (mathd-numbertheory-629-lcm 12 t-value) 3)
        (expt (* 12 t-value) 2))))

(defun mathd-numbertheory-629-no-solution-below-p (limit)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      t
    (let ((candidate (- limit 1)))
      (and
       (not (mathd-numbertheory-629-solution-p candidate))
       (mathd-numbertheory-629-no-solution-below-p candidate)))))

(defun mathd-numbertheory-629-statement ()
  (and
   (mathd-numbertheory-629-solution-p 18)
   (mathd-numbertheory-629-no-solution-below-p 18)))

(value-triple :itpeval-statement-checked)
:q
