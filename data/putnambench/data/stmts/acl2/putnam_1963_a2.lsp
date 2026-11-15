;; Statement-only formalization of PutnamBench corpus artifact putnam_1963_a2:
;; every strictly increasing positive-integer-valued arithmetic function with
;; f(2)=2 that is multiplicative on coprime positive inputs is the identity on
;; the positive integers. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; DEFSTUB introduces an arbitrary unary function conservatively. ACL2
;; functional instantiation makes the theorem generic over every function
;; satisfying the hypotheses, without APPLY$'s tame-function restriction.

(defstub putnam-1963-a2-function (n) t)

(defun putnam-1963-a2-value (n)
  (putnam-1963-a2-function n))

;; For positive M and N, every common divisor is at most M. Thus checking the
;; candidates from M down through 2 is equivalent to gcd(M,N)=1.
(defun putnam-1963-a2-coprime-through-p (m n divisor)
  (declare (xargs :measure (nfix divisor)))
  (if (and (natp divisor)
           (< 1 divisor))
      (and
       (not
        (and
         (equal (mod m divisor) 0)
         (equal (mod n divisor) 0)))
       (putnam-1963-a2-coprime-through-p
        m n (- divisor 1)))
    t))

(defun putnam-1963-a2-coprime-p (m n)
  (and
   (posp m)
   (posp n)
   (putnam-1963-a2-coprime-through-p m n m)))

(defun-sk putnam-1963-a2-positive-natural-values-p ()
  (forall (n)
    (implies
     (natp n)
     (and
      (natp (putnam-1963-a2-value n))
      (< 0 (putnam-1963-a2-value n))))))

(defun-sk putnam-1963-a2-strictly-increasing-p ()
  (forall (i j)
    (implies
     (and
      (posp i)
      (posp j)
      (< i j))
     (<
      (putnam-1963-a2-value i)
      (putnam-1963-a2-value j)))))

(defun-sk putnam-1963-a2-coprime-multiplicative-p ()
  (forall (m n)
    (implies
     (putnam-1963-a2-coprime-p m n)
     (equal
      (putnam-1963-a2-value (* m n))
      (*
       (putnam-1963-a2-value m)
       (putnam-1963-a2-value n))))))

(defun-sk putnam-1963-a2-identity-on-positive-naturals-p ()
  (forall (n)
    (implies
     (posp n)
     (equal
      (putnam-1963-a2-value n)
      n))))

(defun putnambench-putnam-1963-a2-statement ()
  (implies
   (and
    (putnam-1963-a2-positive-natural-values-p)
    (putnam-1963-a2-strictly-increasing-p)
    (equal (putnam-1963-a2-value 2) 2)
    (putnam-1963-a2-coprime-multiplicative-p))
   (putnam-1963-a2-identity-on-positive-naturals-p)))

(value-triple :itpeval-statement-checked)
:q
