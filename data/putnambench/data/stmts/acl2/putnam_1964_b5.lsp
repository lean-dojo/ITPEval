;; Statement-only formalization of PutnamBench corpus artifact putnam_1964_b5:
;; if A is a strictly increasing sequence of positive integers and B(N) is
;; the least common multiple of A(0),...,A(N), then sum 1/B(N) converges.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; DEFSTUB gives arbitrary sequence symbols conservatively.  This is the
;; standard ACL2 representation of a theorem generic over functions and does
;; not impose APPLY$'s tame-function restriction.

(defstub putnam-1964-b5-a (n) t)
(defstub putnam-1964-b5-b (n) t)

(defun putnam-1964-b5-common-multiple-p (x y multiple)
  (and
   (posp x)
   (posp y)
   (posp multiple)
   (equal (mod multiple x) 0)
   (equal (mod multiple y) 0)))

(defun-sk putnam-1964-b5-least-common-multiple-p
    (x y candidate)
  (forall (multiple)
    (implies
     (putnam-1964-b5-common-multiple-p x y multiple)
     (and
      (putnam-1964-b5-common-multiple-p x y candidate)
      (<= candidate multiple)))))

(defun-sk putnam-1964-b5-positive-sequences-p ()
  (forall (n)
    (implies
     (natp n)
     (and
      (posp (putnam-1964-b5-a n))
      (posp (putnam-1964-b5-b n))))))

(defun-sk putnam-1964-b5-strictly-increasing-p ()
  (forall (i j)
    (implies
     (and (natp i) (natp j) (< i j))
     (< (putnam-1964-b5-a i)
        (putnam-1964-b5-a j)))))

(defun-sk putnam-1964-b5-running-lcm-p ()
  (forall (n)
    (implies
     (natp n)
     (putnam-1964-b5-least-common-multiple-p
      (putnam-1964-b5-b n)
      (putnam-1964-b5-a (+ 1 n))
      (putnam-1964-b5-b (+ 1 n))))))

(defun putnam-1964-b5-partial-sum (count)
  (declare (xargs :measure (nfix count)))
  (if (and (natp count) (< 0 count))
      (+ (putnam-1964-b5-partial-sum (- count 1))
         (/ (putnam-1964-b5-b (- count 1))))
    0))

(defun-sk putnam-1964-b5-cauchy-tail-p (epsilon cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp cutoff)
      (<= cutoff m)
      (<= cutoff n))
     (<
      (abs
       (-
        (putnam-1964-b5-partial-sum m)
        (putnam-1964-b5-partial-sum n)))
      epsilon))))

(defun-sk putnam-1964-b5-cauchy-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1964-b5-cauchy-tail-p epsilon cutoff))))

(defun-sk putnam-1964-b5-reciprocal-series-converges-p ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (putnam-1964-b5-cauchy-cutoff-exists-p epsilon))))

(defun putnambench-putnam-1964-b5-statement ()
  (implies
   (and
    (putnam-1964-b5-positive-sequences-p)
    (putnam-1964-b5-strictly-increasing-p)
    (equal (putnam-1964-b5-b 0)
           (putnam-1964-b5-a 0))
    (putnam-1964-b5-running-lcm-p))
   (putnam-1964-b5-reciprocal-series-converges-p)))

(value-triple :itpeval-statement-checked)
:q
