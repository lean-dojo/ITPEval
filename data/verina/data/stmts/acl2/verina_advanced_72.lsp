;; Statement-only formalization of VERINA corpus artifact verina_advanced_72,
;; "singleDigitPrimeFactor": a deterministic natural-number program returns
;; the first divisor among 2, 3, 5, and 7, or zero when none applies, together
;; with its complete correctness contract. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True; the Nat input domain is explicit in the
;; final correctness predicate.

(defun verina-advanced-72-single-digit-prime-factor-precond (n)
  (declare (ignore n))
  t)

;; The proof-valued precondition argument is computationally irrelevant and is
;; erased. On natural inputs, this is exactly the source's ordered conditional
;; chain, including its distinct zero branch.

(defun verina-advanced-72-single-digit-prime-factor (n)
  (if (equal n 0)
      0
    (if (equal (mod n 2) 0)
        2
      (if (equal (mod n 3) 0)
          3
        (if (equal (mod n 5) 0)
            5
          (if (equal (mod n 7) 0)
              7
            0))))))

;; This recursion is List.all (fun divisor => n % divisor != 0) on the fixed
;; source list [2, 3, 5, 7].

(defun verina-advanced-72-all-nondivisors-p (divisors n)
  (declare (xargs :measure (acl2-count divisors)))
  (if (consp divisors)
      (and
       (not (equal (mod n (car divisors)) 0))
       (verina-advanced-72-all-nondivisors-p
        (cdr divisors)
        n))
    (equal divisors nil)))

;; Descending through RESULT-1, ..., 0 checks the same finite set as
;; List.range RESULT. The implication is exactly the source predicate:
;; membership in [2, 3, 5, 7] implies nondivisibility.

(defun verina-advanced-72-earlier-listed-primes-nondivisors-p
    (result n)
  (declare (xargs :measure (nfix result)))
  (if (not (natp result))
      nil
    (if (zp result)
        t
      (let ((x (- result 1)))
        (and
         (implies
          (member-equal x '(2 3 5 7))
          (not (equal (mod n x) 0)))
         (verina-advanced-72-earlier-listed-primes-nondivisors-p
          x
          n))))))

(defun verina-advanced-72-single-digit-prime-factor-postcond
    (n result)
  (and
   (natp n)
   (natp result)
   (member-equal result '(0 2 3 5 7))
   (implies
    (equal result 0)
    (or
     (equal n 0)
     (verina-advanced-72-all-nondivisors-p
      '(2 3 5 7)
      n)))
   (implies
    (not (equal result 0))
    (and
     (not (equal n 0))
     (equal (mod n result) 0)
     (verina-advanced-72-earlier-listed-primes-nondivisors-p
      result
      n)))))

;; This predicate is the unproved final correctness proposition connecting the
;; True precondition and complete postcondition to the exact executable result.

(defun
    verina-advanced-72-single-digit-prime-factor-spec-satisfied-statement
    (n)
  (implies
   (and
    (natp n)
    (verina-advanced-72-single-digit-prime-factor-precond n))
   (verina-advanced-72-single-digit-prime-factor-postcond
    n
    (verina-advanced-72-single-digit-prime-factor n))))

(value-triple :itpeval-statement-checked)
:q
