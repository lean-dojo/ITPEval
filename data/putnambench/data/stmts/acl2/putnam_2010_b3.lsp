;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_b3:
;; every distribution of 2010n balls among 2010 labeled boxes can be made
;; uniform by the prescribed moves exactly when n is at least 1005. This file
;; contains no proof.

(in-package "ACL2")

;; A function Fin 2010 -> Nat is represented exactly by its ordered
;; 2010-tuple of values. The outer DEFUN-SK therefore ranges over every source
;; distribution, without restricting the unbounded natural-number entries.
;;
;; A witness trace is its finite prefix P(0),...,P(T). Conversely, every such
;; list defines the constrained prefix of a source trace and can be extended
;; arbitrarily after T. Thus the internal existential trace below is
;; bidirectionally equivalent to the source's existential P and T. Each call
;; of PUTNAM-2010-B3-STEP-P keeps the source and target boxes existential and
;; internal to that particular move.

(defun putnam-2010-b3-natural-list-p (values)
  (if (consp values)
      (and
       (natp (car values))
       (putnam-2010-b3-natural-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2010-b3-sum (values)
  (if (consp values)
      (+ (car values)
         (putnam-2010-b3-sum (cdr values)))
    0))

(defun putnam-2010-b3-distribution-p (distribution)
  (and
   (true-listp distribution)
   (equal (len distribution) 2010)
   (putnam-2010-b3-natural-list-p distribution)))

(defun putnam-2010-b3-other-boxes-unchanged-p
    (remaining box source target before after)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (or
      (equal box source)
      (equal box target)
      (equal (nth box after)
             (nth box before)))
     (putnam-2010-b3-other-boxes-unchanged-p
      (- remaining 1)
      (+ box 1)
      source
      target
      before
      after))))

(defun putnam-2010-b3-step-witness-p
    (before after source target)
  (let ((amount (+ source 1)))
    (and
     (putnam-2010-b3-distribution-p before)
     (putnam-2010-b3-distribution-p after)
     (natp source)
     (< source 2010)
     (natp target)
     (< target 2010)
     (not (equal source target))
     (<= amount (nth source before))
     (equal (nth source after)
            (- (nth source before) amount))
     (equal (nth target after)
            (+ (nth target before) amount))
     (putnam-2010-b3-other-boxes-unchanged-p
      2010 0 source target before after))))

(defun-sk putnam-2010-b3-step-p (before after)
  (exists (source target)
    (putnam-2010-b3-step-witness-p
     before after source target)))

(defun putnam-2010-b3-trace-steps-p (trace)
  (declare (xargs :measure (acl2-count trace)))
  (if (and (consp trace)
           (consp (cdr trace)))
      (and
       (putnam-2010-b3-step-p
        (car trace)
        (car (cdr trace)))
       (putnam-2010-b3-trace-steps-p
        (cdr trace)))
    t))

(defun putnam-2010-b3-all-equal-p (values n)
  (if (consp values)
      (and
       (equal (car values) n)
       (putnam-2010-b3-all-equal-p (cdr values) n))
    (equal values nil)))

(defun putnam-2010-b3-uniform-distribution-p
    (distribution n)
  (and
   (putnam-2010-b3-distribution-p distribution)
   (putnam-2010-b3-all-equal-p distribution n)))

(defun putnam-2010-b3-trace-witness-p
    (n initial trace)
  (and
   (true-listp trace)
   (consp trace)
   (equal (car trace) initial)
   (putnam-2010-b3-trace-steps-p trace)
   (putnam-2010-b3-uniform-distribution-p
    (car (last trace))
    n)))

(defun-sk putnam-2010-b3-trace-exists-p (n initial)
  (exists (trace)
    (putnam-2010-b3-trace-witness-p
     n initial trace)))

(defun-sk putnam-2010-b3-all-distributions-reachable-p (n)
  (forall (initial)
    (implies
     (and
      (putnam-2010-b3-distribution-p initial)
      (equal
       (putnam-2010-b3-sum initial)
       (* 2010 n)))
     (putnam-2010-b3-trace-exists-p
      n initial))))

(defun putnambench-putnam-2010-b3-statement (n)
  (implies
   (and
    (natp n)
    (< 0 n))
   (iff
    (putnam-2010-b3-all-distributions-reachable-p n)
    (<= 1005 n))))

(value-triple :itpeval-statement-checked)
:q
