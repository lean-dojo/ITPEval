;; Statement-only formalization of PutnamBench corpus artifact putnam_1974_a6:
;; the minimum degree of a monic integer polynomial whose value at every
;; integer is divisible by 1000000 is 25. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Coefficients are stored in ascending degree order. Requiring a list of
;; length D+1 with final coefficient one represents a monic integer
;; polynomial of degree exactly D.
(defun putnam-1974-a6-integer-list-p (values)
  (if (consp values)
      (and
       (integerp (car values))
       (putnam-1974-a6-integer-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1974-a6-polynomial-evaluate
    (coefficients value)
  (if (consp coefficients)
      (+ (car coefficients)
         (* value
            (putnam-1974-a6-polynomial-evaluate
             (cdr coefficients) value)))
    0))

(defun putnam-1974-a6-monic-degree-p
    (coefficients degree)
  (and
   (natp degree)
   (true-listp coefficients)
   (equal (len coefficients) (+ 1 degree))
   (putnam-1974-a6-integer-list-p coefficients)
   (equal (car (last coefficients)) 1)))

;; This is the source's universal condition over every integer input, stated
;; directly rather than replaced by a finite sample or residue enumeration.
(defun-sk putnam-1974-a6-all-values-divisible-p
    (coefficients)
  (forall (value)
    (implies
     (integerp value)
     (equal
      (mod
       (putnam-1974-a6-polynomial-evaluate
        coefficients value)
       1000000)
      0))))

(defun putnam-1974-a6-qualifying-polynomial-p
    (coefficients degree)
  (and
   (putnam-1974-a6-monic-degree-p coefficients degree)
   (putnam-1974-a6-all-values-divisible-p coefficients)))

(defun-sk putnam-1974-a6-qualifying-degree-exists-p
    (degree)
  (exists (coefficients)
    (putnam-1974-a6-qualifying-polynomial-p
     coefficients degree)))

(defun putnam-1974-a6-no-smaller-degree-p (degree-count)
  (declare (xargs :measure (nfix degree-count)))
  (if (zp degree-count)
      t
    (let ((degree (- degree-count 1)))
      (and
       (not
        (putnam-1974-a6-qualifying-degree-exists-p
         degree))
       (putnam-1974-a6-no-smaller-degree-p degree)))))

(defun putnambench-putnam-1974-a6-statement ()
  (and
   (putnam-1974-a6-qualifying-degree-exists-p 25)
   (putnam-1974-a6-no-smaller-degree-p 25)))

(value-triple :itpeval-statement-checked)
:q
