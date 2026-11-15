;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bignum_BigNum_add_cinqtvc: a carry-input addition verification
;; condition for valid base-b integer digit lists and their numeric values.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite proper lists of integers directly represent the
;; source mathematical integers and List Z values.

(defun bignum-add-cin-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (bignum-add-cin-integer-list-p (cdr xs)))))

;; Little-endian base-b value of an integer digit list.

(defun bignum-add-cin-value (base xs)
  (if (endp xs)
      0
    (+ (car xs)
       (* base
          (bignum-add-cin-value base (cdr xs))))))

;; The empty list is valid.  A singleton has a strictly positive digit below
;; the base; every earlier digit may be zero but must remain below the base.

(defun bignum-add-cin-valid-p (base xs)
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
         (bignum-add-cin-valid-p base rest))))))

;; This is the first conjunct of the source VC, preserving its case split and
;; even the explicit arithmetic side conditions occurring in each branch.

(defun bignum-add-cin-branch-invariant-p
    (base n1 n2 cin)
  (if (endp n2)
      (if (endp n1)
          (and
           (bignum-add-cin-valid-p base n2)
           (<= 0 cin)
           (< cin base))
        (and
         (bignum-add-cin-valid-p base n1)
         (<= 0 cin)
         (< cin base)))
    (let ((x (car n2))
          (x1 (cdr n2)))
      (if (endp n1)
          (and
           (bignum-add-cin-valid-p base n2)
           (<= 0 cin)
           (< cin base))
        (let ((x2 (car n1))
              (x3 (cdr n1)))
          (if (< (+ cin x2 x) base)
              (and
               (equal (cdr n1) x3)
               (bignum-add-cin-valid-p base x3)
               (bignum-add-cin-valid-p base x1)
               (<= 0 0)
               (<= 0 1))
            (and
             (equal (cdr n1) x3)
             (bignum-add-cin-valid-p base x3)
             (bignum-add-cin-valid-p base x1)
             (<= 0 1)
             (<= 1 1))))))))

;; The recursive-call output remains an internal existentially quantified
;; integer list, exactly as in the source statement.

(defun-sk bignum-add-cin-step-result-p
    (base tail1 tail2 digit carry result)
  (exists (o1)
    (and
     (bignum-add-cin-integer-list-p o1)
     (and
      (bignum-add-cin-valid-p base o1)
      (equal
       (bignum-add-cin-value base o1)
       (+ (bignum-add-cin-value base tail1)
          (bignum-add-cin-value base tail2)
          carry)))
     (equal result (cons digit o1)))))

(defun bignum-add-cin-result-premise-p
    (base n1 n2 cin result)
  (if (endp n2)
      (if (endp n1)
          (and
           (bignum-add-cin-valid-p base result)
           (equal
            (bignum-add-cin-value base result)
            (+ (bignum-add-cin-value base n2) cin)))
        (and
         (bignum-add-cin-valid-p base result)
         (equal
          (bignum-add-cin-value base result)
          (+ (bignum-add-cin-value base n1) cin))))
    (let ((x (car n2))
          (x1 (cdr n2)))
      (if (endp n1)
          (and
           (bignum-add-cin-valid-p base result)
           (equal
            (bignum-add-cin-value base result)
            (+ (bignum-add-cin-value base n2) cin)))
        (let* ((x2 (car n1))
               (x3 (cdr n1))
               (d (+ cin x2 x)))
          (if (< d base)
              (bignum-add-cin-step-result-p
               base x3 x1 d 0 result)
            (bignum-add-cin-step-result-p
             base x3 x1 (- d base) 1 result)))))))

;; Preserve the universal quantifier over every source-typed result list.

(defun-sk bignum-add-cin-result-continuation-p
    (base n1 n2 cin)
  (forall (result)
    (implies
     (bignum-add-cin-integer-list-p result)
     (implies
      (bignum-add-cin-result-premise-p
       base n1 n2 cin result)
      (and
       (bignum-add-cin-valid-p base result)
       (equal
        (bignum-add-cin-value base result)
        (+ (bignum-add-cin-value base n1)
           (bignum-add-cin-value base n2)
           cin)))))))

(defun ntp4vc-pearl-bignum-bignum-add-cinqtvc-statement
    (base n1 n2 cin)
  (implies
   (and
    (integerp base)
    (< 1 base)
    (bignum-add-cin-integer-list-p n1)
    (bignum-add-cin-integer-list-p n2)
    (integerp cin)
    (bignum-add-cin-valid-p base n1)
    (bignum-add-cin-valid-p base n2)
    (<= 0 cin)
    (<= cin 1))
   (and
    (bignum-add-cin-branch-invariant-p base n1 n2 cin)
    (bignum-add-cin-result-continuation-p
     base n1 n2 cin))))

(value-triple :itpeval-statement-checked)
:q
