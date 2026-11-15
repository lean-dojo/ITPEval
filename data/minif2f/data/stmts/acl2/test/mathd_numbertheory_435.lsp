;; Statement-only formalization of miniF2F artifact mathd_numbertheory_435:
;; a positive natural k satisfying three universal coprimality conditions
;; against consecutive residue classes modulo 6 is at least 5. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-435-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-435-gcd a (- b a)))
            (t
             (mathd-numbertheory-435-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-435-natural-distance (a b)
  (if (< a b)
      (- b a)
    (- a b)))

;; Let d = |k-r|.  For d > 0,
;; gcd(6*n+k, 6*n+r) = gcd(d, 6*n+r), which is periodic in n with
;; period d.  Hence checking 0 <= n < d is equivalent in both directions to
;; checking every natural n.  When d = 0, the universal condition is false.
(defun mathd-numbertheory-435-gcd-one-below-p (k r remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let ((n (- remaining 1)))
      (and
       (equal
        (mathd-numbertheory-435-gcd (+ (* 6 n) k)
                                    (+ (* 6 n) r))
        1)
       (mathd-numbertheory-435-gcd-one-below-p
        k r (- remaining 1))))))

(defun mathd-numbertheory-435-universal-gcd-one-p (k r)
  (let ((period (mathd-numbertheory-435-natural-distance k r)))
    (and (< 0 period)
         (mathd-numbertheory-435-gcd-one-below-p k r period))))

(defun mathd-numbertheory-435-statement (k)
  (implies
   (and (natp k)
        (< 0 k)
        (mathd-numbertheory-435-universal-gcd-one-p k 3)
        (mathd-numbertheory-435-universal-gcd-one-p k 2)
        (mathd-numbertheory-435-universal-gcd-one-p k 1))
   (<= 5 k)))

(value-triple :itpeval-statement-checked)
:q
