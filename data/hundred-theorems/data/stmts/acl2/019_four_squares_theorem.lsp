;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__019, "Four Squares Theorem": every natural number
;; is the sum of four squares of natural numbers. Four bounded searches from
;; n down to 0 encode the existential witnesses. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-019-four-square-with-abc-through-d-p
    (n a b c d)
  (declare (xargs :measure (nfix d)))
  (if (and (natp n)
           (natp a)
           (natp b)
           (natp c)
           (natp d))
      (or (equal n
                 (+ (+ (* a a) (* b b))
                    (+ (* c c) (* d d))))
          (and (not (zp d))
               (hundred-theorems-019-four-square-with-abc-through-d-p
                n a b c (- d 1))))
    nil))

(defun hundred-theorems-019-four-square-with-ab-through-c-p
    (n a b c)
  (declare (xargs :measure (nfix c)))
  (if (and (natp n)
           (natp a)
           (natp b)
           (natp c))
      (or (hundred-theorems-019-four-square-with-abc-through-d-p
           n a b c n)
          (and (not (zp c))
               (hundred-theorems-019-four-square-with-ab-through-c-p
                n a b (- c 1))))
    nil))

(defun hundred-theorems-019-four-square-with-a-through-b-p
    (n a b)
  (declare (xargs :measure (nfix b)))
  (if (and (natp n)
           (natp a)
           (natp b))
      (or (hundred-theorems-019-four-square-with-ab-through-c-p
           n a b n)
          (and (not (zp b))
               (hundred-theorems-019-four-square-with-a-through-b-p
                n a (- b 1))))
    nil))

(defun hundred-theorems-019-four-square-through-a-p (n a)
  (declare (xargs :measure (nfix a)))
  (if (and (natp n)
           (natp a))
      (or (hundred-theorems-019-four-square-with-a-through-b-p
           n a n)
          (and (not (zp a))
               (hundred-theorems-019-four-square-through-a-p
                n (- a 1))))
    nil))

(defun hundred-theorems-019-four-squares-statement (n)
  (implies
   (natp n)
   (hundred-theorems-019-four-square-through-a-p n n)))

(value-triple :itpeval-statement-checked)
:q
