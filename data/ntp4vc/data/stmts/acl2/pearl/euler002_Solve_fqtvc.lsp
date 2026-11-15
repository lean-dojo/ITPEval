;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/euler002_Solve_fqtvc: the integer verification condition for summing
;; even Fibonacci numbers up to a nonnegative bound. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Int.tmod uses division truncated toward zero.  The source only tests parity
;; with divisor 2, but this total definition preserves the imported operation.

(defun ntp4vc-euler002-tdiv (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor
              (abs numerator)
              (abs denominator))))
        (if (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

(defun ntp4vc-euler002-tmod (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (-
       numerator
       (*
        denominator
        (ntp4vc-euler002-tdiv numerator denominator)))
    0))

;; The imported source theories fix integer-valued Fibonacci and partial-sum
;; functions.  Conservative symbols plus explicit predicates reproduce their
;; complete specifications without asserting any theorem.

(defstub ntp4vc-euler002-fib (n) t)
(defstub ntp4vc-euler002-fib-sum-even (m n) t)

(defun ntp4vc-euler002-fib-even (n)
  (ntp4vc-euler002-fib (* 3 n)))

(defun-sk ntp4vc-euler002-fib-context-p ()
  (forall (n)
    (implies
     (integerp n)
     (and
      (integerp (ntp4vc-euler002-fib n))
      (implies
       (<= 0 n)
       (if (equal n 0)
           (equal (ntp4vc-euler002-fib n) 0)
         (if (equal n 1)
             (equal (ntp4vc-euler002-fib n) 1)
           (equal
            (ntp4vc-euler002-fib n)
            (+
             (ntp4vc-euler002-fib (- n 1))
             (ntp4vc-euler002-fib (- n 2)))))))))))

(defun-sk ntp4vc-euler002-sum-context-p ()
  (forall (m n)
    (implies
     (and
      (integerp m)
      (integerp n))
     (and
      (integerp (ntp4vc-euler002-fib-sum-even m n))
      (equal
       (ntp4vc-euler002-fib-sum-even m 0)
       0)
      (implies
       (and
        (<= 0 n)
        (<= (ntp4vc-euler002-fib n) m)
        (equal
         (ntp4vc-euler002-tmod
          (ntp4vc-euler002-fib n)
          2)
         0))
       (equal
        (ntp4vc-euler002-fib-sum-even m (+ n 1))
        (+
         (ntp4vc-euler002-fib-sum-even m n)
         (ntp4vc-euler002-fib n))))
      (implies
       (and
        (<= 0 n)
        (< m (ntp4vc-euler002-fib n))
        (equal
         (ntp4vc-euler002-tmod
          (ntp4vc-euler002-fib n)
          2)
         0))
       (equal
        (ntp4vc-euler002-fib-sum-even m (+ n 1))
        (ntp4vc-euler002-fib-sum-even m n)))
      (implies
       (and
        (<= 0 n)
        (not
         (equal
          (ntp4vc-euler002-tmod
           (ntp4vc-euler002-fib n)
           2)
          0)))
       (equal
        (ntp4vc-euler002-fib-sum-even m (+ n 1))
        (ntp4vc-euler002-fib-sum-even m n)))))))

;; This existential remains inside the false branch of the universally
;; quantified loop obligation, matching the source quantifier scope.

(defun-sk ntp4vc-euler002-termination-witness-p (m k)
  (exists (n1)
    (and
     (integerp n1)
     (equal
      (ntp4vc-euler002-fib-sum-even m k)
      (ntp4vc-euler002-fib-sum-even m n1))
     (< m (ntp4vc-euler002-fib n1)))))

(defun-sk ntp4vc-euler002-loop-obligation-p (m)
  (forall (k n)
    (implies
     (and
      (integerp k)
      (integerp n))
     (implies
      (and
       (<= 0 n)
       (<= 0 k)
       (equal
        (ntp4vc-euler002-fib-even n)
        (ntp4vc-euler002-fib k))
       (equal
        (ntp4vc-euler002-fib-even (+ n 1))
        (ntp4vc-euler002-fib (+ k 3)))
       (<= 0 (ntp4vc-euler002-fib-even n))
       (<
        (ntp4vc-euler002-fib-even n)
        (ntp4vc-euler002-fib-even (+ n 1))))
      (if (<= (ntp4vc-euler002-fib-even n) m)
          (and
           (and
            (<=
             0
             (- m (ntp4vc-euler002-fib-even n)))
            (<
             (-
              m
              (ntp4vc-euler002-fib-even (+ n 1)))
             (- m (ntp4vc-euler002-fib-even n))))
           (<= 0 (+ n 1))
           (<= 0 (+ k 3))
           (equal
            (ntp4vc-euler002-fib-even (+ n 1))
            (ntp4vc-euler002-fib (+ k 3)))
           (equal
            (+
             (* 4 (ntp4vc-euler002-fib-even (+ n 1)))
             (ntp4vc-euler002-fib-even n))
            (ntp4vc-euler002-fib-even (+ n 1 1)))
           (equal
            (+
             (* 4 (ntp4vc-euler002-fib-even (+ n 1)))
             (ntp4vc-euler002-fib-even n))
            (ntp4vc-euler002-fib (+ k 3 3)))
           (equal
            (+
             (ntp4vc-euler002-fib-sum-even m k)
             (ntp4vc-euler002-fib-even n))
            (ntp4vc-euler002-fib-sum-even m (+ k 3)))
           (<=
            0
            (ntp4vc-euler002-fib-even (+ n 1)))
           (<
            (ntp4vc-euler002-fib-even (+ n 1))
            (+
             (* 4 (ntp4vc-euler002-fib-even (+ n 1)))
             (ntp4vc-euler002-fib-even n))))
        (ntp4vc-euler002-termination-witness-p m k))))))

(defun ntp4vc-pearl-euler002-solve-fqtvc-statement (m)
  (implies
   (and
    (integerp m)
    (ntp4vc-euler002-fib-context-p)
    (ntp4vc-euler002-sum-context-p)
    (<= 0 m))
   (and
    (<= 0 0)
    (<= 0 0)
    (equal 0 (ntp4vc-euler002-fib-even 0))
    (equal 0 (ntp4vc-euler002-fib 0))
    (equal 2 (ntp4vc-euler002-fib-even (+ 0 1)))
    (equal 2 (ntp4vc-euler002-fib (+ 0 3)))
    (equal
     0
     (ntp4vc-euler002-fib-sum-even m 0))
    (<= 0 0)
    (< 0 2)
    (ntp4vc-euler002-loop-obligation-p m))))

(value-triple :itpeval-statement-checked)
:q
