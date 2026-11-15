;; Statement-only formalization of PutnamBench corpus artifact putnam_1962_a6:
;; a subset of the rationals closed under addition and multiplication and
;; choosing exactly one of r, -r, and zero is the set of positive rationals.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; DEFSTUB introduces an arbitrary unary predicate conservatively. In ACL2,
;; the resulting theorem is a functional-instantiation schema, so this does
;; not restrict S to executable or APPLY$-tame subsets of the rationals.

(defstub putnam-1962-a6-set-member (r) t)

(defun putnam-1962-a6-member-p (r)
  (if (putnam-1962-a6-set-member r) t nil))

(defun-sk putnam-1962-a6-additively-closed-p ()
  (forall (a b)
    (implies
     (and (rationalp a)
          (rationalp b)
          (putnam-1962-a6-member-p a)
          (putnam-1962-a6-member-p b))
     (putnam-1962-a6-member-p (+ a b)))))

(defun-sk putnam-1962-a6-multiplicatively-closed-p ()
  (forall (a b)
    (implies
     (and (rationalp a)
          (rationalp b)
          (putnam-1962-a6-member-p a)
          (putnam-1962-a6-member-p b))
     (putnam-1962-a6-member-p (* a b)))))

(defun-sk putnam-1962-a6-trichotomy-p ()
  (forall (r)
    (implies
     (rationalp r)
     (let ((r-in-s
            (putnam-1962-a6-member-p r))
           (minus-r-in-s
            (putnam-1962-a6-member-p (- r))))
       (and
        (or r-in-s minus-r-in-s (equal r 0))
        (not (and r-in-s minus-r-in-s))
        (not (and r-in-s (equal r 0)))
        (not (and minus-r-in-s (equal r 0))))))))

(defun-sk putnam-1962-a6-positive-rationals-p ()
  (forall (r)
    (implies
     (rationalp r)
     (iff
      (putnam-1962-a6-member-p r)
      (< 0 r)))))

(defun putnambench-putnam-1962-a6-statement ()
  (implies
   (and
    (putnam-1962-a6-additively-closed-p)
    (putnam-1962-a6-multiplicatively-closed-p)
    (putnam-1962-a6-trichotomy-p))
   (putnam-1962-a6-positive-rationals-p)))

(value-triple :itpeval-statement-checked)
:q
