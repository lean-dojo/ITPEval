;; Statement-only formalization of PutnamBench corpus artifact putnam_1970_a3:
;; the longest nonzero repeated base-10 suffix of a perfect square has length
;; three, first attained by 1444. This file contains no proof.

(in-package "ACL2")

;; The source lists base-10 digits least-significant first.  Its hypothesis on
;; L uniquely makes L(n) the length of the initial run equal to the units digit.
;; Defining that function directly eliminates the arbitrary L without changing
;; the proposition.  Lean's digit list for zero is empty while Isabelle's is
;; [0], but every conclusion involving a square is guarded by a nonzero units
;; digit, so the two definitions agree on every relevant input.
(defun putnam-1970-a3-trailing-run-aux (n digit place fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (not (natp n))
          (not (natp place))
          (zp place)
          (zp fuel)
          (< n place))
      0
    (if (equal (mod (floor n place) 10) digit)
        (+ 1
           (putnam-1970-a3-trailing-run-aux
            n digit (* 10 place) (- fuel 1)))
      0)))

(defun putnam-1970-a3-trailing-run-length (n)
  (if (natp n)
      (putnam-1970-a3-trailing-run-aux n (mod n 10) 1 n)
    0))

(defun putnam-1970-a3-square (n)
  (* n n))

(defun putnam-1970-a3-square-has-nonzero-units-p (n)
  (and (natp n)
       (not (equal (mod (putnam-1970-a3-square n) 10) 0))))

;; The fixed clauses give the source existential witnesses: 38^2 = 1444 has
;; a nonzero units digit and trailing-run length 3.  The parameter N expresses
;; both unbounded universal clauses: no eligible square has a longer run, and
;; every eligible square with run length 3 is at least 1444.
(defun putnambench-putnam-1970-a3-statement (n)
  (and
   (equal (putnam-1970-a3-square 38) 1444)
   (putnam-1970-a3-square-has-nonzero-units-p 38)
   (equal
    (putnam-1970-a3-trailing-run-length
     (putnam-1970-a3-square 38))
    3)
   (implies
    (natp n)
    (and
     (implies
      (putnam-1970-a3-square-has-nonzero-units-p n)
      (<=
       (putnam-1970-a3-trailing-run-length
        (putnam-1970-a3-square n))
       3))
     (implies
      (and
       (putnam-1970-a3-square-has-nonzero-units-p n)
       (equal
        (putnam-1970-a3-trailing-run-length
         (putnam-1970-a3-square n))
        3))
      (<= 1444 (putnam-1970-a3-square n)))))))

(value-triple :itpeval-statement-checked)
:q
