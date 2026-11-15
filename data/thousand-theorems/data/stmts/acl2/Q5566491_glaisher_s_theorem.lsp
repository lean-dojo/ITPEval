;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q5566491, "Glaisher's theorem": for every natural
;; number n and positive natural number m, the number of partitions of n using
;; no part divisible by m equals the number in which every part occurs fewer
;; than m times. This file contains no proof.

(in-package "ACL2")

;; This recurrence counts partitions of REMAINING using positive parts at
;; most PART that are not divisible by M. An admissible part may be omitted or
;; used repeatedly.
(defun q5566491-count-nonmultiples-through-part
    (remaining part m)
  (declare
   (xargs :measure (+ (nfix remaining) (nfix part))))
  (if (and (natp remaining)
           (natp part)
           (posp m))
      (if (zp part)
          (if (zp remaining) 1 0)
        (if (equal (mod part m) 0)
            (q5566491-count-nonmultiples-through-part
             remaining (- part 1) m)
          (if (<= part remaining)
              (+ (q5566491-count-nonmultiples-through-part
                  remaining (- part 1) m)
                 (q5566491-count-nonmultiples-through-part
                  (- remaining part) part m))
            (q5566491-count-nonmultiples-through-part
             remaining (- part 1) m))))
    0))

;; Let C(r,p) count partitions of r with parts at most p and multiplicities
;; below M. The exact coefficient recurrence
;; C(r,p) = C(r,p-1) + C(r-p,p) - C(r-M*p,p-1)
;; removes precisely the cases in which p would occur M times.
(defun q5566491-count-bounded-multiplicity-through-part
    (remaining part m)
  (declare
   (xargs :measure (+ (nfix remaining) (nfix part))))
  (if (and (natp remaining)
           (natp part)
           (posp m))
      (if (zp part)
          (if (zp remaining) 1 0)
        (let ((without-part
               (q5566491-count-bounded-multiplicity-through-part
                remaining (- part 1) m)))
          (if (<= part remaining)
              (- (+ without-part
                    (q5566491-count-bounded-multiplicity-through-part
                     (- remaining part) part m))
                 (if (<= (* m part) remaining)
                     (q5566491-count-bounded-multiplicity-through-part
                      (- remaining (* m part)) (- part 1) m)
                   0))
            without-part)))
    0))

;; Every positive part of a partition of n is at most n, so starting each
;; recurrence at PART = n enumerates the same finite partition classes as the
;; two Finsets in the canonical Lean statement.
(defun q5566491-nonmultiple-partition-count (n m)
  (if (and (natp n) (posp m))
      (q5566491-count-nonmultiples-through-part n n m)
    0))

(defun q5566491-bounded-multiplicity-partition-count (n m)
  (if (and (natp n) (posp m))
      (q5566491-count-bounded-multiplicity-through-part n n m)
    0))

(defun thousand-theorems-q5566491-glaishers-theorem-statement
    (n m)
  (implies
   (and (natp n)
        (natp m)
        (< 0 m))
   (equal
    (q5566491-nonmultiple-partition-count n m)
    (q5566491-bounded-multiplicity-partition-count n m))))

(value-triple :itpeval-statement-checked)
:q
