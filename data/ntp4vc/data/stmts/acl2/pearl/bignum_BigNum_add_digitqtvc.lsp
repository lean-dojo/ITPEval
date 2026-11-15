;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bignum_BigNum_add_digitqtvc: the single-digit addition verification
;; condition for valid base-b integer digit lists and their numeric values.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite proper lists of integers directly represent the
;; source mathematical integers and List Z values.

(defun bignum-add-digit-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (bignum-add-digit-integer-list-p (cdr xs)))))

;; Little-endian base-b value of an integer digit list.

(defun bignum-add-digit-value (base xs)
  (if (endp xs)
      0
    (+ (car xs)
       (* base
          (bignum-add-digit-value base (cdr xs))))))

;; The empty list is valid.  A singleton has a strictly positive digit below
;; the base; every earlier digit may be zero but must remain below the base.

(defun bignum-add-digit-valid-p (base xs)
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
         (bignum-add-digit-valid-p base rest))))))

;; The first source conjunct, including its explicit repeated tail equality
;; and arithmetic side conditions.

(defun bignum-add-digit-branch-invariant-p (base n d)
  (if (endp n)
      t
    (let ((d0 (car n))
          (rest (cdr n)))
      (implies
       (not (< (+ d d0) base))
       (and
        (equal (cdr n) rest)
        (bignum-add-digit-valid-p base rest)
        (<= 0 1)
        (< 1 base))))))

;; In the carry branch, the recursively produced tail remains an internal
;; existentially quantified integer list exactly as in the source statement.

(defun-sk bignum-add-digit-carry-result-p
    (base rest d d0 result)
  (exists (o1)
    (and
     (bignum-add-digit-integer-list-p o1)
     (bignum-add-digit-valid-p base o1)
     (equal
      (bignum-add-digit-value base o1)
      (+ (bignum-add-digit-value base rest) 1))
     (equal
      result
      (cons (- (+ d d0) base) o1)))))

(defun bignum-add-digit-result-premise-p
    (base n d result)
  (if (endp n)
      (if (equal d 0)
          (equal result nil)
        (equal result (list d)))
    (let ((d0 (car n))
          (rest (cdr n)))
      (if (< (+ d d0) base)
          (equal result (cons (+ d d0) rest))
        (bignum-add-digit-carry-result-p
         base rest d d0 result)))))

;; Preserve the universal quantifier over every source-typed result list.

(defun-sk bignum-add-digit-result-continuation-p
    (base n d)
  (forall (result)
    (implies
     (bignum-add-digit-integer-list-p result)
     (implies
      (bignum-add-digit-result-premise-p
       base n d result)
      (and
       (bignum-add-digit-valid-p base result)
       (equal
        (bignum-add-digit-value base result)
        (+ (bignum-add-digit-value base n) d)))))))

(defun ntp4vc-pearl-bignum-bignum-add-digitqtvc-statement
    (base n d)
  (implies
   (and
    (integerp base)
    (< 1 base)
    (bignum-add-digit-integer-list-p n)
    (integerp d)
    (bignum-add-digit-valid-p base n)
    (<= 0 d)
    (< d base))
   (and
    (bignum-add-digit-branch-invariant-p base n d)
    (bignum-add-digit-result-continuation-p base n d))))

(value-triple :itpeval-statement-checked)
:q
