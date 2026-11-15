;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_a6:
;; existence of a partition of the nonnegative integers into two sets having
;; equal ordered distinct-pair representation counts for every sum. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Sets of naturals are represented by tame unary characteristic-function
;; objects. Every such object determines a source set. Conversely, the source
;; existence assertion has tame Thue-Morse characteristic-function witnesses,
;; so this representation is equivalent for this existential proposition and
;; does not replace either set by a finite carrier or table.

(defun putnam-2003-a6-member-p (set n)
  (if (apply$ set (list n))
      t
    nil))

;; REMAINING ranges over s1 = n,n-1,...,0. For each s1, the only possible
;; second summand is s2 = n-s1, so every ordered pair is counted exactly once.
(defun putnam-2003-a6-representation-count-aux
    (set n remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((s1 (- remaining 1))
           (s2 (- n s1)))
      (+
       (if (and
            (not (equal s1 s2))
            (putnam-2003-a6-member-p set s1)
            (putnam-2003-a6-member-p set s2))
           1
         0)
       (putnam-2003-a6-representation-count-aux
        set n (- remaining 1))))))

(defun putnam-2003-a6-representation-count (set n)
  (if (natp n)
      (putnam-2003-a6-representation-count-aux
       set n (+ n 1))
    0))

(defun putnam-2003-a6-partition-and-count-at-p (a b n)
  (and
   ;; Exclusive membership is pointwise equivalent to union UNIV and empty
   ;; intersection.
   (not
    (equal
     (putnam-2003-a6-member-p a n)
     (putnam-2003-a6-member-p b n)))
   (equal
    (putnam-2003-a6-representation-count a n)
    (putnam-2003-a6-representation-count b n))))

(defun-sk putnam-2003-a6-partition-and-counts-agree-p (a b)
  (forall (n)
    (implies
     (natp n)
     (putnam-2003-a6-partition-and-count-at-p a b n))))

(defun-sk putnam-2003-a6-partition-exists-p ()
  (exists (a b)
    (and
     (tamep-functionp a)
     (tamep-functionp b)
     (putnam-2003-a6-partition-and-counts-agree-p a b))))

;; The supplied PutnamBench solution is True, so the source biconditional is
;; exactly the internally quantified existence assertion above.
(defun putnambench-putnam-2003-a6-statement ()
  (putnam-2003-a6-partition-exists-p))

(value-triple :itpeval-statement-checked)
:q
