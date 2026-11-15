;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/gcd_EuclideanAlgorithmIterative_euclidqtvc: the iterative Euclidean
;; algorithm verification condition for nonnegative integers, preserving the
;; greatest common divisor through a remainder step. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The loop invariant gives 0 <= U and the active branch gives 0 < V.
;; Therefore ACL2 MOD is exactly the nonnegative remainder denoted by U % V
;; in the pinned Why3 source.

(defun ntp4vc-euclid-iterative-mod (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (<= 0 numerator)
       (< 0 denominator))
      (mod numerator denominator)
    0))

;; The source integer gcd is the natural-number gcd of absolute values.

(defun ntp4vc-euclid-iterative-gcd-nat (left right)
  (declare
   (xargs :measure
          (+ (nfix left) (nfix right))))
  (if (and (natp left) (natp right))
      (cond
       ((equal left 0) right)
       ((equal right 0) left)
       ((< left right)
        (ntp4vc-euclid-iterative-gcd-nat
         left (- right left)))
       (t
        (ntp4vc-euclid-iterative-gcd-nat
         (- left right) right)))
    0))

(defun ntp4vc-euclid-iterative-gcd (left right)
  (if (and (integerp left) (integerp right))
      (ntp4vc-euclid-iterative-gcd-nat
       (abs left)
       (abs right))
    0))

;; Preserve the source universal quantifier over every integer loop state.

(defun-sk ntp4vc-euclid-iterative-all-states-p
    (u0 v0)
  (forall (v u)
    (implies
     (and
      (integerp v)
      (integerp u))
     (implies
      (and
       (and
        (<= 0 u)
        (<= 0 v))
       (equal
        (ntp4vc-euclid-iterative-gcd u v)
        (ntp4vc-euclid-iterative-gcd u0 v0)))
      (if (not (equal v 0))
          (let ((remainder
                 (ntp4vc-euclid-iterative-mod u v)))
            (and
             (not (equal v 0))
             (and
              (<= 0 v)
              (< remainder v))
             (and
              (<= 0 v)
              (<= 0 remainder))
             (equal
              (ntp4vc-euclid-iterative-gcd
               v remainder)
              (ntp4vc-euclid-iterative-gcd
               u0 v0))))
        (equal
         u
         (ntp4vc-euclid-iterative-gcd u0 v0)))))))

(defun
  ntp4vc-pearl-gcd-euclideanalgorithmiterative-euclidqtvc-statement
  (u0 v0)
  (implies
   (and
    (integerp u0)
    (integerp v0)
    (<= 0 u0)
    (<= 0 v0))
   (and
    (<= 0 u0)
    (<= 0 v0)
    (ntp4vc-euclid-iterative-all-states-p
     u0 v0))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
