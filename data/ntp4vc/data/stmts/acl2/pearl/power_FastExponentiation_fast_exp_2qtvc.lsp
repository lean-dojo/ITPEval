;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/power_FastExponentiation_fast_exp_2qtvc: the fast-exponentiation
;; verification condition for recursive descent and accumulator correctness
;; over nonnegative integer exponents. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3's ComputerDivision operations use integer division truncated toward
;; zero and its associated remainder.

(defun ntp4vc-fast-exp-tdiv (numerator denominator)
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

(defun ntp4vc-fast-exp-tmod (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (-
       numerator
       (*
        denominator
        (ntp4vc-fast-exp-tdiv
         numerator denominator)))
    0))

;; On every exponent reached by this VC, the exponent is nonnegative.  The
;; nfix branch makes the helper total while agreeing with integer power on
;; that source domain.

(defun ntp4vc-fast-exp-power (base exponent)
  (if (and (integerp base) (integerp exponent))
      (expt base (nfix exponent))
    1))

;; Preserve the source's first conjunct, including its explicit nonzero
;; divisor checks and both recursive-call variant obligations.

(defun ntp4vc-fast-exp-descent-vc-p (n)
  (implies
   (not (equal n 0))
   (and
    (not (equal 2 0))
    (if (equal (ntp4vc-fast-exp-tmod n 2) 0)
        (and
         (not (equal 2 0))
         (let ((o1 (ntp4vc-fast-exp-tdiv n 2)))
           (and
            (and (<= 0 n) (< o1 n))
            (<= 0 o1))))
      (let ((o1 (- n 1)))
        (and
         (and (<= 0 n) (< o1 n))
         (<= 0 o1)))))))

;; This is the conditional equation defining a possible recursive result in
;; the second conjunct of the source verification condition.

(defun ntp4vc-fast-exp-result-premise-p
    (n acc x result)
  (if (equal n 0)
      (equal result acc)
    (if (equal (ntp4vc-fast-exp-tmod n 2) 0)
        (equal
         result
         (*
          (ntp4vc-fast-exp-power
           (* x x)
           (ntp4vc-fast-exp-tdiv n 2))
          acc))
      (equal
       result
       (*
        (ntp4vc-fast-exp-power x (- n 1))
        (* x acc))))))

;; Preserve the source universal quantifier over every integer result.

(defun-sk ntp4vc-fast-exp-all-results-p (n acc x)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (ntp4vc-fast-exp-result-premise-p
       n acc x result)
      (equal
       result
       (*
        (ntp4vc-fast-exp-power x n)
        acc))))))

(defun
  ntp4vc-pearl-power-fastexponentiation-fast-exp-2qtvc-statement
  (n acc x)
  (implies
   (and
    (integerp n)
    (integerp acc)
    (integerp x)
    (<= 0 n))
   (and
    (ntp4vc-fast-exp-descent-vc-p n)
    (ntp4vc-fast-exp-all-results-p n acc x))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
