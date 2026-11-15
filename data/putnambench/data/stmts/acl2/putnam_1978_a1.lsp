;; Statement-only formalization of PutnamBench corpus artifact putnam_1978_a1:
;; every 20-element subset of {1, 4, 7, ..., 100} contains two distinct
;; elements whose sum is 104. This file contains no proof.

(in-package "ACL2")

;; The source set S is fixed by its defining equality. Its elements are
;; exactly the integers from 1 through 100 congruent to 1 modulo 3. The source
;; set T has cardinality 20, so a duplicate-free true list of length 20 is a
;; bijective representation after forgetting enumeration order. Every source
;; T has such an enumeration, and every accepted list determines exactly one
;; source T. The recursive search keeps the two existential witnesses internal.

(defun putnam-1978-a1-in-s-p (k)
  (and
   (integerp k)
   (<= 1 k)
   (<= k 100)
   (equal (mod (- k 1) 3) 0)))

(defun putnam-1978-a1-subset-of-s-p (elements)
  (if (consp elements)
      (and
       (putnam-1978-a1-in-s-p (car elements))
       (putnam-1978-a1-subset-of-s-p (cdr elements)))
    (equal elements nil)))

(defun putnam-1978-a1-partner-exists-p (element remaining)
  (if (consp remaining)
      (or
       (and
        (not (equal element (car remaining)))
        (equal (+ element (car remaining)) 104))
       (putnam-1978-a1-partner-exists-p
        element (cdr remaining)))
    nil))

(defun putnam-1978-a1-pair-exists-p (elements)
  (if (consp elements)
      (or
       (putnam-1978-a1-partner-exists-p
        (car elements) (cdr elements))
       (putnam-1978-a1-pair-exists-p (cdr elements)))
    nil))

(defun putnambench-putnam-1978-a1-statement (elements)
  (implies
   (and
    (true-listp elements)
    (no-duplicatesp-equal elements)
    (equal (len elements) 20)
    (putnam-1978-a1-subset-of-s-p elements))
   (putnam-1978-a1-pair-exists-p elements)))

(value-triple :itpeval-statement-checked)
:q
