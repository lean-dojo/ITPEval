;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/power_FastExponentiation_fast_exp_imperativeqtvc: the imperative
;; fast-exponentiation verification condition, including initialization,
;; invariant preservation, loop descent, and final correctness over integer
;; inputs with a nonnegative exponent. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 ComputerDivision uses integer division truncated toward zero and its
;; associated remainder.

(defun ntp4vc-fast-exp-imperative-tdiv (numerator denominator)
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

(defun ntp4vc-fast-exp-imperative-tmod (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (-
       numerator
       (*
        denominator
        (ntp4vc-fast-exp-imperative-tdiv
         numerator denominator)))
    0))

;; Every exponent occurring in the VC is nonnegative. The nfix branch makes
;; this helper total while agreeing exactly with Why3 integer power on that
;; source domain.

(defun ntp4vc-fast-exp-imperative-power (base exponent)
  (if (and (integerp base) (integerp exponent))
      (expt base (nfix exponent))
    1))

;; This predicate is the universally quantified loop obligation. It preserves
;; the invariant premise, the odd/even update split, both explicit nonzero
;; divisor checks, the variant decrease and lower-bound conditions, and the
;; loop-exit conclusion.

(defun ntp4vc-fast-exp-imperative-loop-case-p
    (n x e p r)
  (implies
   (and
    (<= 0 e)
    (equal
     (* r
        (ntp4vc-fast-exp-imperative-power p e))
     (ntp4vc-fast-exp-imperative-power x n)))
   (if (< 0 e)
       (and
        (not (equal 2 0))
        (let ((half
               (ntp4vc-fast-exp-imperative-tdiv e 2)))
          (if
              (equal
               (ntp4vc-fast-exp-imperative-tmod e 2)
               1)
              (and
               (not (equal 2 0))
               (and (<= 0 e) (< half e))
               (<= 0 half)
               (equal
                (*
                 (* r p)
                 (ntp4vc-fast-exp-imperative-power
                  (* p p) half))
                (ntp4vc-fast-exp-imperative-power
                 x n)))
            (and
             (not (equal 2 0))
             (and (<= 0 e) (< half e))
             (<= 0 half)
             (equal
              (* r
                 (ntp4vc-fast-exp-imperative-power
                  (* p p) half))
              (ntp4vc-fast-exp-imperative-power
               x n))))))
     (equal
      r
      (ntp4vc-fast-exp-imperative-power x n)))))

(defun-sk ntp4vc-fast-exp-imperative-all-loop-cases-p (n x)
  (forall (e p r)
    (implies
     (and
      (integerp e)
      (integerp p)
      (integerp r))
     (ntp4vc-fast-exp-imperative-loop-case-p
      n x e p r))))

(defun
  ntp4vc-pearl-power-fastexponentiation-fast-exp-imperativeqtvc-statement
  (n x)
  (implies
   (and
    (integerp n)
    (integerp x)
    (<= 0 n))
   (and
    (<= 0 n)
    (equal
     (* 1
        (ntp4vc-fast-exp-imperative-power x n))
     (ntp4vc-fast-exp-imperative-power x n))
    (ntp4vc-fast-exp-imperative-all-loop-cases-p
     n x))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
