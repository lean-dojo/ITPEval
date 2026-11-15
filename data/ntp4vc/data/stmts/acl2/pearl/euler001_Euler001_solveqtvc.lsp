;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/euler001_Euler001_solveqtvc: the positive-integer Euler 1
;; verification condition equating the sum of multiples of 3 or 5 below n
;; with its inclusion-exclusion closed formula. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This is integer division truncated toward zero, matching Lean Int.tdiv and
;; Isabelle cdiv on the mathematical integers.

(defun ntp4vc-euler001-tdiv (numerator denominator)
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

(defun ntp4vc-euler001-tmod (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (-
       numerator
       (*
        denominator
        (ntp4vc-euler001-tdiv numerator denominator)))
    0))

;; The imported source theory fixes an integer-valued function for the sum of
;; nonnegative integers below the argument that are divisible by 3 or 5.
;; The conservative symbol and explicit laws reproduce that source context.

(defstub ntp4vc-euler001-sum-multiple-3-5-lt (n) t)

(defun-sk ntp4vc-euler001-sum-recurrence-p ()
  (forall (k)
    (implies
     (integerp k)
     (and
      (integerp
       (ntp4vc-euler001-sum-multiple-3-5-lt k))
      (implies
       (and
        (<= 0 k)
        (not
         (equal
          (ntp4vc-euler001-tmod k 3)
          0))
        (not
         (equal
          (ntp4vc-euler001-tmod k 5)
          0)))
       (equal
        (ntp4vc-euler001-sum-multiple-3-5-lt
         (+ k 1))
        (ntp4vc-euler001-sum-multiple-3-5-lt k)))
      (implies
       (and
        (<= 0 k)
        (or
         (equal
          (ntp4vc-euler001-tmod k 3)
          0)
         (equal
          (ntp4vc-euler001-tmod k 5)
          0)))
       (equal
        (ntp4vc-euler001-sum-multiple-3-5-lt
         (+ k 1))
        (+
         (ntp4vc-euler001-sum-multiple-3-5-lt k)
         k)))))))

(defun ntp4vc-euler001-sum-context-p ()
  (and
   (equal
    (ntp4vc-euler001-sum-multiple-3-5-lt 0)
    0)
   (ntp4vc-euler001-sum-recurrence-p)))

(defun ntp4vc-pearl-euler001-euler001-solveqtvc-statement (n)
  (implies
   (and
    (integerp n)
    (ntp4vc-euler001-sum-context-p)
    (<= 1 n))
   (and
    (not (equal 3 0))
    (let ((n3
           (ntp4vc-euler001-tdiv
            (- n 1)
            3)))
      (and
       (not (equal 5 0))
       (let ((n5
              (ntp4vc-euler001-tdiv
               (- n 1)
               5)))
         (and
          (not (equal 15 0))
          (let ((n15
                 (ntp4vc-euler001-tdiv
                  (- n 1)
                  15)))
            (and
             (not (equal 2 0))
             (equal
              (ntp4vc-euler001-tdiv
               (-
                (+
                 (* 3 n3 (+ n3 1))
                 (* 5 n5 (+ n5 1)))
                (* 15 n15 (+ n15 1)))
               2)
              (ntp4vc-euler001-sum-multiple-3-5-lt
               n)))))))))))

(value-triple :itpeval-statement-checked)
:q
