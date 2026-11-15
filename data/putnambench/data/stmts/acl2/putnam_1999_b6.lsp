;; Statement-only formalization of PutnamBench corpus artifact putnam_1999_b6:
;; a finite set of integers greater than one satisfying the stated gcd
;; covering condition contains two elements whose gcd is prime. This file
;; contains no proof.

(in-package "ACL2")

;; A duplicate-free true list is a bijective enumeration of the source finite
;; set. Since every element is greater than one, the product below is positive
;; and is a common multiple of every element.

(defun putnam-1999-b6-all-greater-than-one-p (elements)
  (if (consp elements)
      (and
       (integerp (car elements))
       (< 1 (car elements))
       (putnam-1999-b6-all-greater-than-one-p
        (cdr elements)))
    (equal elements nil)))

(defun putnam-1999-b6-product (elements)
  (if (consp elements)
      (* (car elements)
         (putnam-1999-b6-product (cdr elements)))
    1))

(defun putnam-1999-b6-gcd (left right)
  (declare (xargs :measure (+ (nfix left) (nfix right))))
  (if (and (natp left) (natp right))
      (cond
       ((equal left 0) right)
       ((equal right 0) left)
       ((< left right)
        (putnam-1999-b6-gcd left (- right left)))
       (t
        (putnam-1999-b6-gcd (- left right) right)))
    0))

(defun putnam-1999-b6-residue-covered-p (elements residue)
  (if (consp elements)
      (let* ((s (car elements))
             (common-divisor
              (putnam-1999-b6-gcd s residue)))
        (or
         (equal common-divisor 1)
         (equal common-divisor s)
         (putnam-1999-b6-residue-covered-p
          (cdr elements) residue)))
    nil))

;; For each positive s in the list, gcd(s,n) depends only on n modulo s.
;; The list product is divisible by every s, so checking its complete residue
;; system is equivalent to the source hypothesis quantified over all integers.
(defun putnam-1999-b6-all-residues-covered-p
    (elements remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let ((residue (- remaining 1)))
      (and
       (putnam-1999-b6-residue-covered-p
        elements residue)
       (putnam-1999-b6-all-residues-covered-p
        elements residue)))))

(defun putnam-1999-b6-no-divisor-through-p
    (number candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or
       (not (natp candidate))
       (<= candidate 1))
      t
    (and
     (not (equal (mod number candidate) 0))
     (putnam-1999-b6-no-divisor-through-p
      number (- candidate 1)))))

(defun putnam-1999-b6-prime-p (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-1999-b6-no-divisor-through-p
    number (- number 1))))

(defun putnam-1999-b6-prime-gcd-with-some-p
    (s candidates)
  (if (consp candidates)
      (or
       (putnam-1999-b6-prime-p
        (putnam-1999-b6-gcd s (car candidates)))
       (putnam-1999-b6-prime-gcd-with-some-p
        s (cdr candidates)))
    nil))

(defun putnam-1999-b6-prime-gcd-pair-p
    (remaining elements)
  (if (consp remaining)
      (or
       (putnam-1999-b6-prime-gcd-with-some-p
        (car remaining) elements)
       (putnam-1999-b6-prime-gcd-pair-p
        (cdr remaining) elements))
    nil))

(defun putnambench-putnam-1999-b6-statement (elements)
  (implies
   (and
    (true-listp elements)
    (no-duplicatesp-equal elements)
    (putnam-1999-b6-all-greater-than-one-p elements)
    (let ((period (putnam-1999-b6-product elements)))
      (putnam-1999-b6-all-residues-covered-p
       elements period)))
   (putnam-1999-b6-prime-gcd-pair-p
    elements elements)))

(value-triple :itpeval-statement-checked)
:q
