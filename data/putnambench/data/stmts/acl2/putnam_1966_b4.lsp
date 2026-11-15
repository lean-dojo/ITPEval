;; Statement-only formalization of PutnamBench artifact putnam_1966_b4:
;; every set of m*n+1 positive integers contains either an (m+1)-element
;; divisibility antichain or an (n+1)-element divisibility chain. This file
;; contains no proof.

(in-package "ACL2")

;; The source set is finite by its cardinality hypothesis. A duplicate-free
;; true list therefore gives an arbitrary enumeration of it, and forgetting
;; list order recovers the source set. The searches below consider every
;; extensional subset of the required size, so the witness remains internally
;; existential rather than becoming an extra statement parameter.

(defun putnam-1966-b4-positive-natural-list-p (values)
  (if (consp values)
      (and
       (natp (car values))
       (< 0 (car values))
       (putnam-1966-b4-positive-natural-list-p
        (cdr values)))
    (equal values nil)))

(defun putnam-1966-b4-divides-p (divisor multiple)
  (and
   (integerp divisor)
   (< 0 divisor)
   (integerp multiple)
   (equal (mod multiple divisor) 0)))

(defun putnam-1966-b4-nondivisible-from-p
    (value remaining)
  (if (consp remaining)
      (and
       (not
        (putnam-1966-b4-divides-p
         value (car remaining)))
       (not
        (putnam-1966-b4-divides-p
         (car remaining) value))
       (putnam-1966-b4-nondivisible-from-p
        value (cdr remaining)))
    t))

(defun putnam-1966-b4-antichain-p (values)
  (if (consp values)
      (and
       (putnam-1966-b4-nondivisible-from-p
        (car values) (cdr values))
       (putnam-1966-b4-antichain-p (cdr values)))
    t))

(defun putnam-1966-b4-chain-from-p (value remaining)
  (if (consp remaining)
      (and
       (if (< value (car remaining))
           (putnam-1966-b4-divides-p
            value (car remaining))
         (putnam-1966-b4-divides-p
          (car remaining) value))
       (putnam-1966-b4-chain-from-p
        value (cdr remaining)))
    t))

(defun putnam-1966-b4-chain-p (values)
  (if (consp values)
      (and
       (putnam-1966-b4-chain-from-p
        (car values) (cdr values))
       (putnam-1966-b4-chain-p (cdr values)))
    t))

(defun putnam-1966-b4-antichain-subset-exists-p
    (chosen remaining needed)
  (declare (xargs :measure (len remaining)))
  (cond
   ((zp needed)
    (putnam-1966-b4-antichain-p chosen))
   ((endp remaining) nil)
   (t
    (or
     (putnam-1966-b4-antichain-subset-exists-p
      (cons (car remaining) chosen)
      (cdr remaining)
      (- needed 1))
     (putnam-1966-b4-antichain-subset-exists-p
      chosen
      (cdr remaining)
      needed)))))

(defun putnam-1966-b4-chain-subset-exists-p
    (chosen remaining needed)
  (declare (xargs :measure (len remaining)))
  (cond
   ((zp needed)
    (putnam-1966-b4-chain-p chosen))
   ((endp remaining) nil)
   (t
    (or
     (putnam-1966-b4-chain-subset-exists-p
      (cons (car remaining) chosen)
      (cdr remaining)
      (- needed 1))
     (putnam-1966-b4-chain-subset-exists-p
      chosen
      (cdr remaining)
      needed)))))

(defun putnambench-putnam-1966-b4-statement (m n values)
  (implies
   (and
    (natp m)
    (natp n)
    (true-listp values)
    (no-duplicatesp-equal values)
    (putnam-1966-b4-positive-natural-list-p values)
    (equal (len values) (+ (* m n) 1)))
   (or
    (putnam-1966-b4-antichain-subset-exists-p
     nil values (+ m 1))
    (putnam-1966-b4-chain-subset-exists-p
     nil values (+ n 1)))))

(value-triple :itpeval-statement-checked)
:q
