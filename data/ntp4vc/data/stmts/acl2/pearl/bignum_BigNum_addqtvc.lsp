;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bignum_BigNum_addqtvc: the addition verification condition for valid
;; base-b integer digit lists and removal of a trailing additive zero.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite proper lists of integers directly represent the
;; source mathematical integers and List Z values.

(defun bignum-add-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (bignum-add-integer-list-p (cdr xs)))))

;; Little-endian base-b value of an integer digit list.

(defun bignum-add-value (base xs)
  (if (endp xs)
      0
    (+ (car xs)
       (* base
          (bignum-add-value base (cdr xs))))))

;; The empty list is valid.  A singleton has a strictly positive digit below
;; the base; every earlier digit may be zero but must remain below the base.

(defun bignum-add-valid-p (base xs)
  (if (endp xs)
      t
    (let ((digit (car xs))
          (rest (cdr xs)))
      (if (endp rest)
          (and
           (< 0 digit)
           (< digit base))
        (and
         (<= 0 digit)
         (< digit base)
         (bignum-add-valid-p base rest))))))

;; Preserve the universal quantifier over every source-typed result list.

(defun-sk bignum-add-result-continuation-p
    (base n1 n2)
  (forall (result)
    (implies
     (bignum-add-integer-list-p result)
     (implies
      (and
       (bignum-add-valid-p base result)
       (equal
        (bignum-add-value base result)
        (+ (bignum-add-value base n1)
           (bignum-add-value base n2)
           0)))
      (and
       (bignum-add-valid-p base result)
       (equal
        (bignum-add-value base result)
        (+ (bignum-add-value base n1)
           (bignum-add-value base n2))))))))

(defun ntp4vc-pearl-bignum-bignum-addqtvc-statement
    (base n1 n2)
  (implies
   (and
    (integerp base)
    (< 1 base)
    (bignum-add-integer-list-p n1)
    (bignum-add-integer-list-p n2)
    (bignum-add-valid-p base n1)
    (bignum-add-valid-p base n2))
   (and
    (bignum-add-valid-p base n1)
    (bignum-add-valid-p base n2)
    (<= 0 0)
    (<= 0 1)
    (bignum-add-result-continuation-p base n1 n2))))

(value-triple :itpeval-statement-checked)
:q
