;; Statement-only formalization of PutnamBench corpus artifact putnam_2000_b1:
;; integer triples with an odd entry admit an integer linear combination
;; that is odd on at least four sevenths of the indices. This file contains
;; no proof.

(in-package "ACL2")

;; Lists of length N represent the three functions on Fin N exactly. Only
;; parity matters in an integer linear combination modulo 2, so any integer
;; coefficient triple can be replaced by its residues in {0,1}^3, and every
;; such residue triple is itself an integer triple. Thus the eight cases in
;; the statement are bidirectionally equivalent to the source existential
;; quantifier over integers r, s, and t. The scaled inequality
;; 7*count >= 4*N is exactly count >= (4*N)/7 over the reals.

(defun putnam-2000-b1-integer-list-p (values)
  (if (consp values)
      (and
       (integerp (car values))
       (putnam-2000-b1-integer-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2000-b1-input-odd-p (a b c)
  (declare (xargs :measure (len a)))
  (if (consp a)
      (and
       (or
        (not (equal (mod (car a) 2) 0))
        (not (equal (mod (car b) 2) 0))
        (not (equal (mod (car c) 2) 0)))
       (putnam-2000-b1-input-odd-p
        (cdr a) (cdr b) (cdr c)))
    (and (equal a nil)
         (equal b nil)
         (equal c nil))))

(defun putnam-2000-b1-odd-count (a b c r s coefficient-t)
  (declare (xargs :measure (len a)))
  (if (consp a)
      (+
       (if
        (not
         (equal
          (mod
           (+ (* r (car a))
              (* s (car b))
              (* coefficient-t (car c)))
           2)
          0))
        1
        0)
       (putnam-2000-b1-odd-count
        (cdr a) (cdr b) (cdr c) r s coefficient-t))
    0))

(defun putnam-2000-b1-four-sevenths-p
    (n a b c r s coefficient-t)
  (<=
   (* 4 n)
   (* 7
      (putnam-2000-b1-odd-count
       a b c r s coefficient-t))))

(defun putnambench-putnam-2000-b1-statement (n a b c)
  (implies
   (and
    (posp n)
    (true-listp a)
    (true-listp b)
    (true-listp c)
    (equal (len a) n)
    (equal (len b) n)
    (equal (len c) n)
    (putnam-2000-b1-integer-list-p a)
    (putnam-2000-b1-integer-list-p b)
    (putnam-2000-b1-integer-list-p c)
    (putnam-2000-b1-input-odd-p a b c))
   (or
    (putnam-2000-b1-four-sevenths-p n a b c 0 0 0)
    (putnam-2000-b1-four-sevenths-p n a b c 0 0 1)
    (putnam-2000-b1-four-sevenths-p n a b c 0 1 0)
    (putnam-2000-b1-four-sevenths-p n a b c 0 1 1)
    (putnam-2000-b1-four-sevenths-p n a b c 1 0 0)
    (putnam-2000-b1-four-sevenths-p n a b c 1 0 1)
    (putnam-2000-b1-four-sevenths-p n a b c 1 1 0)
    (putnam-2000-b1-four-sevenths-p n a b c 1 1 1))))

(value-triple :itpeval-statement-checked)
:q
