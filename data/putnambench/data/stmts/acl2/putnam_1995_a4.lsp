;; Statement-only formalization of PutnamBench corpus artifact putnam_1995_a4:
;; a cyclic necklace of n integer labels with total n - 1 has a cut at which
;; every nonempty initial sum is at most its zero-based endpoint. This file
;; contains no proof.

(in-package "ACL2")

;; An integer true list of length n is bijective with a function Fin n -> Z.
;; The bounded searches below keep the source's existential cut and universal
;; prefix endpoint internal to the statement encoding.

(defun putnam-1995-a4-integer-list-p (values)
  (if (consp values)
      (and
       (integerp (car values))
       (putnam-1995-a4-integer-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1995-a4-list-sum (values)
  (if (consp values)
      (+ (car values)
         (putnam-1995-a4-list-sum (cdr values)))
    0))

(defun putnam-1995-a4-cyclic-prefix-sum
    (necklace cut count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (nth
        (mod (+ cut (- count 1))
             (len necklace))
        necklace)
       (putnam-1995-a4-cyclic-prefix-sum
        necklace cut (- count 1)))))

(defun putnam-1995-a4-all-prefix-bounds-p
    (necklace cut endpoint)
  (declare (xargs :measure (nfix endpoint)))
  (and
   (<= (putnam-1995-a4-cyclic-prefix-sum
        necklace cut (+ endpoint 1))
       endpoint)
   (if (zp endpoint)
       t
     (putnam-1995-a4-all-prefix-bounds-p
      necklace cut (- endpoint 1)))))

(defun putnam-1995-a4-cut-exists-through-p
    (necklace cut)
  (declare (xargs :measure (nfix cut)))
  (or
   (putnam-1995-a4-all-prefix-bounds-p
    necklace cut (- (len necklace) 1))
   (if (zp cut)
       nil
     (putnam-1995-a4-cut-exists-through-p
      necklace (- cut 1)))))

(defun putnambench-putnam-1995-a4-statement
    (n necklace)
  (implies
   (and
    (posp n)
    (true-listp necklace)
    (equal (len necklace) n)
    (putnam-1995-a4-integer-list-p necklace)
    (equal (putnam-1995-a4-list-sum necklace)
           (- n 1)))
   (putnam-1995-a4-cut-exists-through-p
    necklace (- n 1))))

(value-triple :itpeval-statement-checked)
:q
